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
open Loc

type ast_transform = statement loc -> statement loc

let block = function
  | [] -> { txt = Block []; addr = -1 }
  | [ stmt ] -> stmt
  | stmts -> { txt = Block stmts; addr = (List.last_exn stmts).addr }

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
  let rec update { txt; addr } =
    let txt' =
      match txt with
      | Label (Address addr) -> (
          match Hashtbl.find targets addr with
          | Some i -> Label (Address i)
          | None -> Block [] (* remove unused label *))
      | IfElse (e, stmt1, stmt2) -> IfElse (e, update stmt1, update stmt2)
      | While (cond, body) -> While (cond, update body)
      | DoWhile (body, cond) -> DoWhile (update body, cond)
      | For (init, cond, inc, body) -> For (init, cond, inc, update body)
      | Block stmts ->
          (List.map stmts ~f:update
          |> List.filter ~f:(function
               | { txt = Block []; _ } -> false
               | _ -> true)
          |> block)
            .txt
      | Switch (id, e, stmt) -> Switch (id, e, update stmt)
      | Goto (addr, x) -> Goto (Hashtbl.find_exn targets addr, x)
      | stmt -> stmt
    in
    { txt = txt'; addr }
  in
  update stmt

let recover_loop_initializer stmt =
  let rec reduce left = function
    | [] -> left
    | s1 :: ({ txt = For (None, None, None, _); _ } as s2) :: right ->
        (* Do not transform loops where both cond and inc are empty. *)
        reduce (s2 :: s1 :: left) right
    | { txt = Expression (AssignOp _ as init); addr }
      :: { txt = For (None, cond, inc, body); _ }
      :: right ->
        reduce ({ txt = For (Some init, cond, inc, body); addr } :: left) right
    | { txt = VarDecl (var, Some (inst, expr)); addr }
      :: { txt = For (None, cond, inc, body); _ }
      :: right ->
        reduce
          ({
             txt =
               For
                 ( Some (AssignOp (inst, PageRef (LocalPage, var), expr)),
                   cond,
                   inc,
                   body );
             addr;
           }
          :: { txt = VarDecl (var, None); addr }
          :: left)
          right
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_redundant_return { txt; addr } =
  {
    txt =
      (match txt with
      | Block ({ txt = Return None; _ } :: stmts) -> Block stmts
      | Block ({ txt = Return _; _ } :: ({ txt = Return _; _ } :: _ as stmts))
        ->
          Block stmts
      | stmt -> stmt);
    addr;
  }

let remove_implicit_array_free stmt =
  let process_block stmts =
    let vars =
      List.rev_filter_map stmts ~f:(function
        | { txt = VarDecl (({ type_ = Array _; _ } as var), _); _ } -> Some var
        | _ -> None)
    in
    let rec remove_free vars stmts =
      match (vars, stmts) with
      | [], _ -> stmts
      | ( var :: vars,
          {
            txt =
              Expression (Call (Builtin (A_FREE, PageRef (LocalPage, v)), []));
            _;
          }
          :: stmts )
        when phys_equal var v ->
          remove_free vars stmts
      (* For switch statements, free is inserted before break *)
      | _, ({ txt = Break; _ } as stmt) :: stmts ->
          stmt :: remove_free vars stmts
      | _ ->
          Stdio.eprintf "remove_implicit_array_free: no Array.free for %s\n"
            ([%show: Ain.Variable.t list] vars);
          stmts
    in
    remove_free vars stmts
  in
  match stmt with
  | { txt = Block stmts; addr } ->
      { txt = Block (List.map stmts ~f:(map_block ~f:process_block)); addr }
  | stmt -> map_block stmt ~f:process_block

let remove_array_initializer_call = function
  | { txt = Block stmts; addr } -> (
      match List.rev stmts with
      | { txt = Expression (Call (Method (Page StructPage, f), [])); _ } :: rest
        when String.is_suffix f.name ~suffix:"@2" ->
          { txt = Block (List.rev rest); addr }
      | _ -> { txt = Block stmts; addr })
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
    | ({ txt = Expression (Call (SysCall 4, [])); _ } as unlockpeek) :: right
      -> (
        match left with
        | (( { txt = VarDecl ({ type_ = Ref _; _ }, Some _); _ }
           | { txt = Expression (AssignOp (PSEUDO_REF_ASSIGN, _, _)); _ } ) as
           stmt)
          :: { txt = Expression (Call (SysCall 3, [])); _ }
          :: left ->
            reduce (stmt :: left) right
        | { txt = Expression (Call (SysCall 3, [])); _ } :: left ->
            reduce left right
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
    | { txt = Msg (m, None); addr }
      :: { txt = Expression (Call _ as e); _ }
      :: right ->
        reduce ({ txt = Msg (m, Some e); addr } :: left) right
    | stmt :: right -> reduce (stmt :: left) right
  in
  map_block stmt ~f:(fun stmts -> reduce [] (List.rev stmts))

let remove_optional_arguments =
  map_expr ~f:(function
    | Call ((Builtin (PSEUDO_A_NUMOF1, _) as f), [ Number 1l ]) -> Call (f, [])
    | Call ((Builtin (A_SORT, _) as f), [ Null ]) -> Call (f, [])
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
