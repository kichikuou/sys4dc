(* Copyright (C) 2024 kichikuou <KichikuouChrome@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://gnu.org/licenses/>.
 *)

open Base
open Ast

type ast_transform = statement -> statement

let block = function [ stmt ] -> stmt | stmts -> Block stmts

let rename_labels stmt =
  let targets = ref [] in
  walk_statement stmt ~f:(function
    | Goto (addr, _) when not (List.mem !targets addr ~equal:( = )) ->
        targets := addr :: !targets
    | _ -> ());
  let targets =
    List.rev !targets
    |> List.mapi ~f:(fun i addr -> (addr, i))
    |> Hashtbl.of_alist_exn (module Int)
  in
  let rec update = function
    | Label (Address addr) -> (
        match Hashtbl.find targets addr with
        | Some i -> Label (Address i)
        | None -> Block [] (* remove unused label *))
    | IfElse (e, stmt1, stmt2) -> IfElse (e, update stmt1, update stmt2)
    | While (cond, body) -> While (cond, update body)
    | DoWhile (body, cond) -> DoWhile (update body, cond)
    | For (init, cond, inc, body) -> For (init, cond, inc, update body)
    | Block stmts ->
        List.map stmts ~f:update
        |> List.filter ~f:(function Block [] -> false | _ -> true)
        |> block
    | Switch (id, e, stmt) -> Switch (id, e, update stmt)
    | Goto (addr, x) -> Goto (Hashtbl.find_exn targets addr, x)
    | stmt -> stmt
  in
  update stmt

let recover_loop_initializer stmt =
  let rec reduce left = function
    | [] -> left
    | s1 :: (For (None, None, None, _) as s2) :: right ->
        (* Do not transform loops where both cond and inc are empty. *)
        reduce (s2 :: s1 :: left) right
    | Expression (AssignOp _ as init) :: For (None, cond, inc, body) :: right ->
        reduce (For (Some init, cond, inc, body) :: left) right
    | VarDecl (var, Some (inst, expr)) :: For (None, cond, inc, body) :: right
      ->
        reduce
          (For
             ( Some (AssignOp (inst, PageRef (LocalPage, var), expr)),
               cond,
               inc,
               body )
          :: VarDecl (var, None)
          :: left)
          right
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_redundant_return = function
  | Block (Return None :: stmts) -> Block stmts
  | Block (Return _ :: (Return _ :: _ as stmts)) -> Block stmts
  | stmt -> stmt

let remove_implicit_array_free stmt =
  let process_block stmts =
    let vars =
      List.rev_filter_map stmts ~f:(function
        | VarDecl (({ type_ = Array _; _ } as var), _) -> Some var
        | _ -> None)
    in
    let rec remove_free vars stmts =
      match (vars, stmts) with
      | [], _ -> stmts
      | ( var :: vars,
          Expression (Call (Builtin (A_FREE, PageRef (LocalPage, v)), []))
          :: stmts )
        when phys_equal var v ->
          remove_free vars stmts
      (* For switch statements, free is inserted before break *)
      | _, Break :: stmts -> Break :: remove_free vars stmts
      | _ ->
          Stdio.eprintf "remove_implicit_array_free: no Array.free for %s\n"
            ([%show: Ain.Variable.t list] vars);
          stmts
    in
    remove_free vars stmts
  in
  match stmt with
  | Block stmts -> Block (List.map stmts ~f:(map_block ~f:process_block))
  | stmt -> map_block stmt ~f:process_block

let remove_array_initializer_call = function
  | Block stmts -> (
      match List.rev stmts with
      | Expression (Call (Method (Page StructPage, f), [])) :: rest
        when String.is_suffix f.name ~suffix:"@2" ->
          Block (List.rev rest)
      | _ -> Block stmts)
  | stmt -> stmt

let remove_dummy_variable_assignment stmt =
  let is_dummy_var v = String.is_prefix v.Ain.Variable.name ~prefix:"<dummy " in
  let strip_dummy_assignment = function
    | AssignOp (PSEUDO_REF_ASSIGN, PageRef (LocalPage, v), expr)
      when is_dummy_var v ->
        expr
    | expr -> expr
  in
  map_expr ~f:strip_dummy_assignment stmt
  |> map_stmt ~f:(function
       | VarDecl (v, Some (_, e)) when is_dummy_var v -> Expression e
       | stmt -> stmt)

let remove_generated_lockpeek stmt =
  let rec reduce left = function
    | [] -> left
    | (Expression (Call (SysCall 4, [])) as unlockpeek) :: right -> (
        match left with
        | (( VarDecl ({ type_ = Ref _; _ }, Some _)
           | Expression (AssignOp (PSEUDO_REF_ASSIGN, _, _)) ) as stmt)
          :: Expression (Call (SysCall 3, []))
          :: left ->
            reduce (stmt :: left) right
        | Expression (Call (SysCall 3, [])) :: left -> reduce left right
        | _ -> reduce (unlockpeek :: left) right)
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_vardecl_default_rhs stmt =
  map_stmt stmt ~f:(function
    | VarDecl (v, Some (_, (Null | DerefRef NullRef))) -> VarDecl (v, None)
    | s -> s)

let fold_newline_func_to_msg stmt =
  let rec reduce left = function
    | [] -> left
    | Msg (m, None) :: Expression (Call _ as e) :: right ->
        reduce (Msg (m, Some e) :: left) right
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_cast =
  (* Only casts that don't change the meaning should be removed, but for now we
     remove them all to match AinDecompiler. *)
  map_expr ~f:(function
    | UnaryOp ((FTOI | ITOF | ITOLI | STOI), expr) -> expr
    | expr -> expr)

let remove_optional_arguments =
  map_expr ~f:(function
    | Call ((Builtin (A_NUMOF, _) as f), [ Number 1l ]) -> Call (f, [])
    | Call ((Builtin (A_FIND, _) as f), [ a; b; c; Null ]) ->
        Call (f, [ a; b; c ])
    | Call ((Builtin2 (FTOS, _) as f), [ Number -1l ]) -> Call (f, [])
    | expr -> expr)

let simplify_boolean_expr =
  map_expr ~f:(function
    | UnaryOp (NOT, BinaryOp (GT, e1, e2)) -> BinaryOp (LTE, e1, e2)
    | UnaryOp (NOT, BinaryOp (LT, e1, e2)) -> BinaryOp (GTE, e1, e2)
    | UnaryOp (NOT, BinaryOp (GTE, e1, e2)) -> BinaryOp (LT, e1, e2)
    | UnaryOp (NOT, BinaryOp (LTE, e1, e2)) -> BinaryOp (GT, e1, e2)
    | UnaryOp (NOT, BinaryOp (EQUALE, e1, e2)) -> BinaryOp (NOTE, e1, e2)
    | UnaryOp (NOT, BinaryOp (NOTE, e1, e2)) -> BinaryOp (EQUALE, e1, e2)
    | BinaryOp (NOTE, e, Boolean false) -> e
    | expr -> expr)
