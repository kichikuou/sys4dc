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
open Instructions
open BasicBlock

module CFG = struct
  module L = Core.Doubly_linked

  type t = fragment basic_block L.t

  let of_list = L.of_list
  let to_list = L.to_list
  let value = Option.map ~f:L.Elt.value
  let value_exn node = L.Elt.value (Option.value_exn node)

  let next cfg = function
    | None -> raise (Invalid_argument "next Null")
    | Some elt -> L.next cfg elt

  let prev cfg = function
    | None -> raise (Invalid_argument "prev Null")
    | Some elt -> L.prev cfg elt

  let first = L.first_elt
  let last = L.last_elt
  let is_end = Option.is_none
  let node_equal node node' = Option.equal L.Elt.equal node node'

  let insert_before cfg node value =
    Some (L.insert_before cfg (Option.value_exn node) value)

  let insert_last cfg value = Some (L.insert_last cfg value)
  let remove cfg node = L.remove cfg (Option.value_exn node)
  let set node value = L.Elt.set (Option.value_exn node) value

  let rec iterate cfg node end_node f =
    if node_equal node end_node then ()
    else (
      f (value_exn node);
      iterate cfg (next cfg node) end_node f)

  let rec find cfg node ~next ~f =
    match value node with
    | None -> None
    | Some v -> if f v then node else find cfg (next cfg node) ~next ~f

  let find_forward cfg node ~f = find cfg node ~next ~f
  let find_backward cfg node ~f = find cfg node ~next:prev ~f
  let by_address addr bb = bb.addr = addr

  let by_jump_target addr = function
    | { code = Jump target, _; _ } -> target = addr
    | _ -> false

  let rec splice_to_list cfg begin_node end_node =
    if node_equal begin_node end_node then []
    else
      let nxt = next cfg begin_node in
      remove cfg begin_node;
      value_exn begin_node :: splice_to_list cfg nxt end_node

  let splice cfg begin_node end_node =
    L.of_list (splice_to_list cfg begin_node end_node)
end

let negate = function UnaryOp (NOT, e) -> e | e -> UnaryOp (NOT, e)
let block = function [ stmt ] -> stmt | stmts -> Block stmts

let add_labels labels stmts =
  if List.is_empty labels then stmts
  else stmts @ List.map labels ~f:(fun l -> Label l)

let decrement_nr_jump_srcs bb n = bb.nr_jump_srcs <- bb.nr_jump_srcs - n

let remove_jump bb =
  match bb with
  | { code = Jump _, stmts; _ } ->
      { bb with code = (Seq, stmts); end_addr = bb.end_addr - 6 }
  | _ -> failwith "no Jump terminator to remove"

let rec stmt_list_to_expr = function
  | [ Expression e ] -> e
  | Expression e :: stmts -> BinaryOp (PSEUDO_COMMA, stmt_list_to_expr stmts, e)
  | stmts ->
      Printf.failwithf "Cannot convert statement %s to an expression"
        (show_statement (Block stmts))
        ()

let do_collapse bbs =
  List.concat_map (List.rev bbs) ~f:(fun bb ->
      let stmts =
        match bb.code with
        | Jump addr, stmts -> Goto (addr, bb.end_addr) :: stmts
        | Seq, stmts -> stmts
        | _ ->
            Printf.failwithf "Cannot convert basic block to statement: %s"
              ([%show: BasicBlock.t] bb)
              ()
      in
      let labels =
        if bb.nr_jump_srcs > List.length bb.labels then
          Address bb.addr :: bb.labels
        else bb.labels
      in
      add_labels labels stmts)
  |> block

let recover_else (cfg : CFG.t) =
  (if Ain.ain.ifthen_optimized then
     let region_end_addr =
       match CFG.value (CFG.last cfg) with Some bb -> bb.end_addr | None -> -1
     in
     let match_if = function
       | {
           code =
             ( Seq,
               IfElse (cond, Block (Goto (addr, _) :: then_block), Block [])
               :: stmts );
           _;
         } ->
           Some (cond, addr, then_block, stmts)
       | { code = Seq, IfElse (cond, Goto (addr, _), Block []) :: stmts; _ } ->
           Some (cond, addr, [], stmts)
       | _ -> None
     in
     let rec scan node =
       match CFG.value node with
       | None -> ()
       | Some bb -> (
           match match_if bb with
           | Some (cond, addr, then_block, stmts) ->
               if addr = region_end_addr then (
                 let else_stmt =
                   CFG.splice_to_list cfg (CFG.next cfg node) None
                   |> do_collapse
                 in
                 CFG.set node
                   {
                     bb with
                     code =
                       (Seq, IfElse (cond, block then_block, else_stmt) :: stmts);
                     end_addr = region_end_addr;
                   };
                 scan node)
               else
                 let target =
                   CFG.(find_forward ~f:(by_address addr) cfg (next cfg node))
                 in
                 if CFG.is_end target then scan (CFG.prev cfg node)
                 else
                   let target_bb = CFG.value_exn target in
                   let else_stmt =
                     CFG.splice_to_list cfg (CFG.next cfg node) target
                     |> do_collapse
                   in
                   CFG.set node
                     {
                       bb with
                       code =
                         ( Seq,
                           IfElse (cond, block then_block, else_stmt) :: stmts
                         );
                       end_addr = target_bb.addr;
                     };
                   decrement_nr_jump_srcs target_bb 1;
                   scan node
           | None -> scan (CFG.prev cfg node))
     in
     scan (CFG.last cfg));
  do_collapse (CFG.to_list cfg)

type break_continue_record = {
  continue_addr : int;
  mutable break_addr : int;
  mutable nr_continues : int;
  mutable nr_breaks : int;
}

(* Convenient default value. *)
let break_continue_record =
  { continue_addr = -1; break_addr = -1; nr_continues = 0; nr_breaks = 0 }

let generate_break_continue record cfg =
  let rec replace_stmt = function
    | VarDecl _ as stmt -> stmt
    | Expression _ as stmt -> stmt
    | Label _ as stmt -> stmt
    | IfElse (e, stmt1, stmt2) ->
        IfElse (e, replace_stmt stmt1, replace_stmt stmt2)
    | While _ as stmt -> stmt
    | DoWhile _ as stmt -> stmt
    | For _ as stmt -> stmt
    | Break -> Break
    | Continue -> failwith "cannot happen"
    | Goto (addr, _) as stmt ->
        if addr = record.continue_addr then (
          record.nr_continues <- record.nr_continues + 1;
          Continue)
        else if addr = record.break_addr then (
          record.nr_breaks <- record.nr_breaks + 1;
          Break)
        else stmt
    | Return _ as stmt -> stmt
    | ScenarioJump _ as stmt -> stmt
    | Msg _ as stmt -> stmt
    | Assert _ as stmt -> stmt
    | Block stmts -> Block (List.map stmts ~f:replace_stmt)
    | Switch (id, e, body) as stmt ->
        if record.continue_addr = -1 then stmt
        else
          let break_addr_orig = record.break_addr in
          record.break_addr <- -1;
          let body = replace_stmt body in
          record.break_addr <- break_addr_orig;
          Switch (id, e, body)
  in
  let replace_bb bb =
    match bb with
    | { code = Jump addr, stmts; _ } ->
        let stmts = List.map stmts ~f:replace_stmt in
        if addr = record.continue_addr then (
          record.nr_continues <- record.nr_continues + 1;
          { bb with code = (Seq, Continue :: stmts) })
        else if addr = record.break_addr then (
          record.nr_breaks <- record.nr_breaks + 1;
          { bb with code = (Seq, Break :: stmts) })
        else { bb with code = (Jump addr, stmts) }
    | { code = terminator, stmts; _ } ->
        { bb with code = (terminator, List.map stmts ~f:replace_stmt) }
  in
  let rec aux node =
    match CFG.value node with
    | None -> ()
    | Some bb ->
        CFG.set node (replace_bb bb);
        aux (CFG.next cfg node)
  in
  aux (CFG.first cfg);
  cfg

(* True if there's a break/continue statement that is not nested in a while/for/switch *)
let rec has_break_continue cfg begin_node end_node =
  let rec test_stmt = function
    | VarDecl _ -> false
    | Expression _ -> false
    | Label _ -> false
    | IfElse (_, stmt1, stmt2) -> test_stmt stmt1 || test_stmt stmt2
    | While (_, _) -> false
    | DoWhile (_, _) -> false
    | For (_, _, _, _) -> false
    | Break -> true
    | Continue -> true
    | Goto _ -> false
    | Return _ -> false
    | ScenarioJump _ -> false
    | Msg _ -> false
    | Assert _ -> false
    | Block stmts -> List.exists stmts ~f:test_stmt
    | Switch (_, _, _) -> false
  in
  if CFG.node_equal begin_node end_node then false
  else
    let { code = _, stmts; _ } = CFG.value_exn begin_node in
    test_stmt (Block stmts)
    || has_break_continue cfg (CFG.next cfg begin_node) end_node

(* Returns true if any variable is declared between block_begin and block_end
   and used after block_end. *)
let has_escaping_vars cfg block_begin block_end =
  let vars = ref [] in
  CFG.iterate cfg block_begin block_end (fun { code = _, stmts; _ } ->
      List.iter stmts ~f:(function
        | VarDecl (v, _) -> vars := v :: !vars
        | _ -> ()));
  if List.is_empty !vars then false
  else
    let result = ref false in
    CFG.iterate cfg block_end None (fun bb ->
        (match bb with
        | { code = (Seq | Jump _ | DoWhile0 _), stmts; _ } -> stmts
        | { code = Branch (_, e), stmts; _ } -> Expression e :: stmts
        | { code = Switch0 (_, e), stmts; _ } -> Expression e :: stmts)
        |> block
        |> Ast.walk ~lvalue_cb:(function
             | PageRef (_, v) when Stdlib.List.memq v !vars -> result := true
             | _ -> ()));
    !result

let recover_forever_loop (cfg : CFG.t) =
  let rec scan node =
    match CFG.value node with
    | None -> ()
    | Some ({ code = Jump addr, _; _ } as bb) ->
        let target = CFG.(find_backward ~f:(by_address addr) cfg node) in
        if
          CFG.is_end target
          || has_break_continue cfg target (CFG.next cfg node)
          (* If creating a loop causes out-of-scope use of a variable, don't create it.
              For example, the jump to label1 below should not be converted to a loop:
                label:
                  int x = 42;
                  goto label;
                  f(x);
          *)
          || has_escaping_vars cfg target (CFG.next cfg node)
        then scan (CFG.next cfg node)
        else
          let target_bb = CFG.value_exn target in
          let new_node = CFG.insert_before cfg target target_bb in
          CFG.set target { target_bb with labels = []; nr_jump_srcs = 0 };
          CFG.set node (remove_jump bb);
          let body =
            CFG.splice cfg target (CFG.next cfg node)
            |> generate_break_continue
                 {
                   break_continue_record with
                   continue_addr = addr;
                   break_addr = bb.end_addr;
                 }
            |> recover_else
          in
          decrement_nr_jump_srcs target_bb 1;
          CFG.set new_node
            {
              target_bb with
              end_addr = bb.end_addr;
              code = (Seq, [ For (None, None, None, body) ]);
            };
          scan (CFG.next cfg new_node)
    | Some _ -> scan (CFG.next cfg node)
  in
  scan (CFG.first cfg);
  recover_else cfg

let collapse = recover_forever_loop

(* switch statement.
    bb0: Switch0 (expr)
    bb1: Jump bbk
    ...
    bbk: ...
    => switch (expr) { bb2..bb(k-1) };
*)
let reduce_switch cfg node0 =
  let node1 = CFG.next cfg node0 in
  let bb0 = CFG.value_exn node0 in
  let bb1 = CFG.value_exn node1 in
  match (bb0, bb1) with
  | ( { code = Switch0 (id, expr), stmts0; _ },
      { code = Jump switch_end_addr, []; _ } ) ->
      let body_head = CFG.next cfg node1 in
      let body_end =
        CFG.(find_forward ~f:(by_address switch_end_addr) cfg body_head)
      in
      let body_end_bb = CFG.value_exn body_end in
      let case_labels, other_labels =
        List.partition_tf body_end_bb.labels ~f:(function
          | CaseInt (id', _) when id = id' -> true
          | CaseStr (id', _) when id = id' -> true
          | Default id' when id = id' -> true
          | _ -> false)
      in
      if not (List.is_empty case_labels) then
        CFG.insert_before cfg body_end
          {
            addr = switch_end_addr;
            end_addr = switch_end_addr;
            code = (Seq, []);
            labels = case_labels;
            nr_jump_srcs = List.length case_labels;
          }
        |> ignore;
      let bc_record =
        {
          break_continue_record with
          continue_addr = -1;
          break_addr = switch_end_addr;
        }
      in
      let body =
        CFG.splice cfg body_head body_end
        |> generate_break_continue bc_record
        |> collapse
      in
      CFG.set node0
        {
          bb0 with
          code = (Seq, Switch (id, expr, body) :: stmts0);
          end_addr = switch_end_addr;
        };
      CFG.set body_end
        {
          body_end_bb with
          labels = other_labels;
          nr_jump_srcs =
            body_end_bb.nr_jump_srcs - 1 - bc_record.nr_breaks
            - List.length case_labels;
        };
      CFG.remove cfg node1
  | _ -> failwith "unexpected basic block after Switch0"

let reduce_if_then cfg node0 branch_target =
  (* if (expr) stmt; (optimized) *)
  let bb0 = CFG.value_exn node0 in
  match bb0 with
  | { code = Branch (branch_target_addr, expr), stmts0; _ } ->
      let then_stmt =
        CFG.splice cfg (CFG.next cfg node0) branch_target |> collapse
      in
      CFG.set node0
        {
          (CFG.value_exn node0) with
          code = (Seq, IfElse (expr, then_stmt, Block []) :: stmts0);
          end_addr = branch_target_addr;
        };
      decrement_nr_jump_srcs (CFG.value_exn branch_target) 1
  | _ -> failwith "cannot happen"

(* do-while loop (seen in Pascha C++)
   bb0:
   ...
   bbk: expr, Branch bb0

   => do { bb0..bbk-1 } while (expr)
*)
let reduce_backward_branch cfg nodek branch_target =
  (* We need to reduce the body block first, so here we just insert a marker
     before the jump target. *)
  let bbk = CFG.value_exn nodek in
  let bb0 = CFG.value_exn branch_target in
  CFG.insert_before cfg branch_target
    {
      addr = bb0.addr;
      end_addr = bb0.addr;
      code = (DoWhile0 bbk.addr, []);
      labels = [];
      nr_jump_srcs = 0;
    }
  |> ignore

let reduce_do_while cfg marker_node =
  match CFG.value_exn marker_node with
  | { code = DoWhile0 bbk_addr, []; _ } -> (
      let node0 = CFG.next cfg marker_node in
      let nodek = CFG.(find_forward ~f:(by_address bbk_addr) cfg node0) in
      let bb0 = CFG.value_exn node0 in
      let bbk = CFG.value_exn nodek in
      match bbk with
      | { code = Branch (_, expr), stmts0; _ } ->
          CFG.set nodek { bbk with code = (Seq, stmts0) };
          let body =
            CFG.splice cfg node0 (CFG.next cfg nodek)
            |> generate_break_continue
                 {
                   break_continue_record with
                   continue_addr = bbk.addr;
                   break_addr = bbk.end_addr;
                 }
            |> collapse
          in
          CFG.set marker_node
            {
              bb0 with
              code = (Seq, [ DoWhile (body, negate expr) ]);
              end_addr = bbk.end_addr;
              nr_jump_srcs = bb0.nr_jump_srcs - 1;
            }
      | _ -> failwith "cannot happen")
  | _ -> failwith "cannot happen"

let reduce_forward_branch cfg node0 branch_target =
  let bb0 = CFG.value_exn node0 in
  let node_before_branch_target = CFG.prev cfg branch_target in
  match (bb0, CFG.value node_before_branch_target) with
  | ( { code = Branch (branch_target_addr, expr), stmts0; _ },
      Some ({ code = Jump label1, _; _ } as bb_before_branch_target) ) ->
      if label1 = branch_target_addr then (
        (* if (expr) stmt; (unoptimized) *)
        CFG.set node_before_branch_target (remove_jump bb_before_branch_target);
        let then_stmt =
          CFG.splice cfg (CFG.next cfg node0) branch_target |> collapse
        in
        CFG.set node0
          {
            bb0 with
            code = (Seq, IfElse (expr, then_stmt, Block []) :: stmts0);
            end_addr = branch_target_addr;
          };
        decrement_nr_jump_srcs (CFG.value_exn branch_target) 2)
      else if label1 > branch_target_addr then (
        if Ain.ain.ifthen_optimized then reduce_if_then cfg node0 branch_target
        else
          (* if (expr) stmt1; else stmt2; *)
          let else_end_addr = label1 in
          let else_end =
            CFG.(
              find_forward ~f:(by_address else_end_addr) cfg
                (next cfg branch_target))
          in
          if CFG.is_end else_end then
            Printf.failwithf "basic block %d not found" else_end_addr ()
          else
            CFG.set node_before_branch_target
              (remove_jump bb_before_branch_target);
          decrement_nr_jump_srcs (CFG.value_exn branch_target) 1;
          let then_stmt =
            CFG.splice cfg (CFG.next cfg node0) branch_target |> collapse
          in
          let else_stmt = CFG.splice cfg branch_target else_end |> collapse in
          CFG.set node0
            {
              bb0 with
              code = (Seq, IfElse (expr, then_stmt, else_stmt) :: stmts0);
              end_addr = else_end_addr;
            };
          decrement_nr_jump_srcs (CFG.value_exn else_end) 1)
      else if label1 = bb0.addr && List.is_empty stmts0 then (
        (* while (expr) stmt; *)
        CFG.set node_before_branch_target (remove_jump bb_before_branch_target);
        let body =
          CFG.splice cfg (CFG.next cfg node0) branch_target
          |> generate_break_continue
               {
                 break_continue_record with
                 continue_addr = bb0.addr;
                 break_addr = branch_target_addr;
               }
          |> collapse
        in
        CFG.set node0
          {
            bb0 with
            code = (Seq, [ While (expr, body) ]);
            end_addr = branch_target_addr;
            nr_jump_srcs = bb0.nr_jump_srcs - 1;
          };
        decrement_nr_jump_srcs (CFG.value_exn branch_target) 1)
      else if bb0.addr < label1 && label1 < branch_target_addr then
        let node1 = CFG.next cfg node0 in
        let node2 = CFG.next cfg node1 in
        match (CFG.value_exn node1, CFG.value_exn node2) with
        | ( { code = Jump label3, []; _ },
            { addr = label1'; code = Jump label0, inc; end_addr = label3'; _ } )
          when label0 = bb0.addr && label1 = label1' && label3 = label3' ->
            (* for-loop.
                bb0: loop_expr, Branch bbk
                bb1: Jump bb3
                bb2: inc_expr, Jump bb0
                bb3: ...
                ...
                bbk-1: ..., JUMP bb2
                bbk:
                => for (; loop_expr; inc_expr) { bb3..bbk-1 }
            *)
            let inc_expr =
              if List.is_empty inc then None else Some (stmt_list_to_expr inc)
            in
            CFG.set node_before_branch_target
              (remove_jump bb_before_branch_target);
            decrement_nr_jump_srcs (CFG.value_exn (CFG.next cfg node2)) 1;
            let body =
              CFG.splice cfg (CFG.next cfg node2) branch_target
              |> generate_break_continue
                   {
                     break_continue_record with
                     continue_addr = label1;
                     break_addr = branch_target_addr;
                   }
              |> collapse
            in
            CFG.set node0
              {
                bb0 with
                code = (Seq, [ For (None, Some expr, inc_expr, body) ]);
                nr_jump_srcs = bb0.nr_jump_srcs - 1;
                end_addr = branch_target_addr;
              };
            CFG.remove cfg node1;
            CFG.remove cfg node2;
            decrement_nr_jump_srcs (CFG.value_exn branch_target) 1
        | _ ->
            if Ain.ain.ifthen_optimized then
              reduce_if_then cfg node0 branch_target
            else failwith "unexpected flow structure"
      else if Ain.ain.ifthen_optimized && label1 <= bb0.addr then
        reduce_if_then cfg node0 branch_target
      else
        Printf.failwithf "unrecognized control structure:\n%s"
          ([%show: fragment basic_block list]
             (CFG.splice_to_list cfg node0 None))
          ()
  | _ -> reduce_if_then cfg node0 branch_target

(* for-loop without conditional expression.
    bb0: JUMP bb2
    bb1: inc_stmt, JUMP bb0
    bb2: ...
    ...
    bbk: ..., JUMP bb1
    => for (;; inc_stmt) { bb2..bbk }
*)
let reduce_jump cfg node0 =
  let bb0 = CFG.value_exn node0 in
  let node1 = CFG.next cfg node0 in
  match (bb0, CFG.value node1) with
  | ( { code = Jump body_addr, []; _ },
      Some
        ({ code = Jump cond_addr, inc_stmts; end_addr = body_addr'; _ } as bb1)
    )
    when body_addr = body_addr' && cond_addr = bb0.addr -> (
      let node2 = CFG.next cfg node1 in
      match CFG.(find_forward ~f:(by_jump_target bb1.addr) cfg node2) with
      | Some _ as nodek ->
          let break_addr = (CFG.value_exn nodek).end_addr in
          let inc_expr =
            if List.is_empty inc_stmts then None
            else Some (stmt_list_to_expr inc_stmts)
          in
          CFG.set nodek (remove_jump (CFG.value_exn nodek));
          let body =
            CFG.splice cfg node2 (CFG.next cfg nodek)
            |> generate_break_continue
                 {
                   break_continue_record with
                   continue_addr = bb1.addr;
                   break_addr;
                 }
            |> collapse
          in
          CFG.set node0
            {
              bb0 with
              end_addr = break_addr;
              code = (Seq, [ For (None, None, inc_expr, body) ]);
              nr_jump_srcs = bb0.nr_jump_srcs - 1;
            };
          CFG.remove cfg node1
      | None -> ())
  | _ -> ()

let reduce cfg node0 =
  let bb0 = CFG.value_exn node0 in
  match bb0 with
  | { code = Switch0 _, _; _ } -> reduce_switch cfg node0
  | { code = Branch (addr, _), _; _ } ->
      let target =
        CFG.(find_forward ~f:(by_address addr) cfg (next cfg node0))
      in
      if not (CFG.is_end target) then reduce_forward_branch cfg node0 target
      else
        let target = CFG.(find_backward ~f:(by_address addr) cfg node0) in
        if not (CFG.is_end target) then reduce_backward_branch cfg node0 target
        else Printf.failwithf "basic block %d not found" addr ()
  | { code = Jump _, _; _ } -> reduce_jump cfg node0
  | { code = DoWhile0 _, _; _ } -> reduce_do_while cfg node0
  | _ -> ()

let analyze bbs =
  let cfg = CFG.of_list bbs in
  (* Add a dummy exit block. *)
  let end_addr =
    match CFG.value (CFG.last cfg) with Some bb -> bb.end_addr | None -> -1
  in
  CFG.insert_last cfg
    {
      addr = end_addr;
      end_addr;
      code = (Seq, []);
      labels = [];
      nr_jump_srcs = 0;
    }
  |> ignore;
  let rec scan node =
    if CFG.is_end node then collapse cfg
    else (
      reduce cfg node;
      scan (CFG.prev cfg node))
  in
  scan (CFG.last cfg)
