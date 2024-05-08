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

open Core
open Format
open Type
open Ast
open Instructions

type variable = { v : Ain.Variable.t; dims : Ast.expr list }

type function_t = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  name : string;
  body : Ast.statement;
}

type struct_t = {
  struc : Ain.Struct.t;
  mutable members : variable list;
  mutable methods : function_t list;
}

type op_prec =
  | PREC_COMMA
  | PREC_ASSIGN
  | PREC_QUESTION
  | PREC_LOGOR
  | PREC_LOGAND
  | PREC_BITOR
  | PREC_BITXOR
  | PREC_BITAND
  | PREC_EQUAL
  | PREC_ORDER
  | PREC_BITSHIFT
  | PREC_ADD
  | PREC_MUL
  | PREC_UNARY
  | PREC_DOT
[@@deriving enum]

(* suppress "unused value" warning *)
let _ = (min_op_prec, max_op_prec, op_prec_of_enum)

type op_associativity = Left | Right

let prec_value p = op_prec_to_enum p * 2
let print_indent n ppf = pp_print_string ppf (String.make n '\t')
let comma ppf _ = fprintf ppf ", "
let open_paren prec op_prec ppf = if prec > op_prec then pp_print_string ppf "("

let close_paren prec op_prec ppf =
  if prec > op_prec then pp_print_string ppf ")"

let format_float x =
  let s = Printf.sprintf "%f" x in
  let i = ref (String.length s - 1) in
  while Char.equal (String.get s !i) '0' do
    Int.decr i
  done;
  if Char.equal (String.get s !i) '.' then Int.incr i;
  String.sub s ~pos:0 ~len:(!i + 1)

let escape_map = [ ('\t', 't'); ('\r', 'r'); ('\n', 'n'); ('\x00', '0') ]

let escape_sq =
  String.Escaping.escape_gen_exn ~escape_char:'\\'
    ~escapeworthy_map:(('\'', '\'') :: escape_map)
  |> unstage

let escape_dq =
  String.Escaping.escape_gen_exn ~escape_char:'\\'
    ~escapeworthy_map:(('"', '"') :: escape_map)
  |> unstage

let pr_char ppf c =
  if UtfSjis.is_sjis c then (
    let buf = Buffer.create 2 in
    Buffer.add_char buf (Char.of_int_exn (c land 0xff));
    if c > 0xff then Buffer.add_char buf (Char.of_int_exn (c lsr 8));
    fprintf ppf "'%s'" (escape_sq (UtfSjis.sjis2utf (Buffer.contents buf))))
  else fprintf ppf "%d" c

let strip_class_name s =
  match String.lsplit2 s ~on:'@' with None -> s | Some (_, right) -> right

let pr_array_rank ppf rank = if rank > 1 then fprintf ppf "%@%d" rank

let rec pr_array_dims ppf = function
  | [] -> ()
  | Number n :: dims ->
      fprintf ppf "[%ld]" n;
      pr_array_dims ppf dims
  | _ -> failwith "pr_array_dims: non-number"

let pr_initval ppf (v : Ain.Variable.t) =
  match v.init_val with
  | None -> ()
  | Some (Int n) -> (
      match v.type_ with
      | Bool -> fprintf ppf " = %s" (if Int32.(n = 0l) then "false" else "true")
      | Ref _ -> fprintf ppf " = %s" Ain.ain.glob.(Int32.to_int_exn n).name
      | _ -> fprintf ppf " = %ld" n)
  | Some (Float f) -> fprintf ppf " = %s" (format_float f)
  | Some (Ain.Variable.String s) -> fprintf ppf " = \"%s\"" (escape_dq s)

type operator = { sym : string; prec : int; lprec : int; rprec : int }

let make_op sym prec assoc =
  let p = prec_value prec in
  match assoc with
  | Left -> { sym; prec = p; lprec = p; rprec = p + 1 }
  | Right -> { sym; prec = p; lprec = p + 1; rprec = p }

let incdec_op = function
  | Increment -> make_op "++" PREC_UNARY Left
  | Decrement -> make_op "--" PREC_UNARY Left

let operator insn =
  match insn with
  | PSEUDO_COMMA -> make_op "," PREC_COMMA Left
  | OBJSWAP _ -> make_op "<=>" PREC_ASSIGN Left
  | ASSIGN | F_ASSIGN | LI_ASSIGN | S_ASSIGN | R_ASSIGN | SR_ASSIGN | DG_ASSIGN
  | DG_SET | PSEUDO_FT_ASSIGNS _ ->
      make_op "=" PREC_ASSIGN Right
  | PSEUDO_REF_ASSIGN -> make_op "<-" PREC_ASSIGN Right
  | PLUSA | F_PLUSA | LI_PLUSA | S_PLUSA | S_PLUSA2 | DG_PLUSA ->
      make_op "+=" PREC_ASSIGN Right
  | MINUSA | F_MINUSA | LI_MINUSA | DG_MINUSA -> make_op "-=" PREC_ASSIGN Right
  | MULA | F_MULA | LI_MULA -> make_op "*=" PREC_ASSIGN Right
  | DIVA | F_DIVA | LI_DIVA -> make_op "/=" PREC_ASSIGN Right
  | MODA | LI_MODA -> make_op "%=" PREC_ASSIGN Right
  | ORA -> make_op "|=" PREC_ASSIGN Right
  | ANDA -> make_op "&=" PREC_ASSIGN Right
  | XORA -> make_op "^=" PREC_ASSIGN Right
  | PSEUDO_LOGOR -> make_op "||" PREC_LOGOR Left
  | PSEUDO_LOGAND -> make_op "&&" PREC_LOGAND Left
  | OR -> make_op "|" PREC_BITOR Left
  | XOR -> make_op "^" PREC_BITXOR Left
  | AND -> make_op "&" PREC_BITAND Left
  | EQUALE | S_EQUALE | F_EQUALE -> make_op "==" PREC_EQUAL Left
  | NOTE | S_NOTE | F_NOTE -> make_op "!=" PREC_EQUAL Left
  | R_EQUALE -> make_op "===" PREC_EQUAL Left
  | R_NOTE -> make_op "!==" PREC_EQUAL Left
  | LT | F_LT | S_LT -> make_op "<" PREC_ORDER Left
  | LTE | F_LTE | S_LTE -> make_op "<=" PREC_ORDER Left
  | GT | F_GT | S_GT -> make_op ">" PREC_ORDER Left
  | GTE | F_GTE | S_GTE -> make_op ">=" PREC_ORDER Left
  | LSHIFT -> make_op "<<" PREC_BITSHIFT Left
  | RSHIFT -> make_op ">>" PREC_BITSHIFT Left
  | ADD | F_ADD | LI_ADD | S_ADD -> make_op "+" PREC_ADD Left
  | SUB | F_SUB | LI_SUB -> make_op "-" PREC_ADD Left
  | MUL | F_MUL | LI_MUL -> make_op "*" PREC_MUL Left
  | DIV | F_DIV | LI_DIV -> make_op "/" PREC_MUL Left
  | MOD | LI_MOD | S_MOD _ -> make_op "%" PREC_MUL Left
  | INV | F_INV -> make_op "-" PREC_UNARY Right
  | NOT -> make_op "!" PREC_UNARY Right
  | COMPL -> make_op "~" PREC_UNARY Right
  | op ->
      Printf.failwithf "cannot print operator for %s" (show_instruction op) ()

let rec pr_type ppf = function
  | Any -> failwith "unresolved type"
  | Char -> failwith "variables cannot have Char type"
  | Int -> pp_print_string ppf "int"
  | Float -> pp_print_string ppf "float"
  | String -> pp_print_string ppf "string"
  | Bool -> pp_print_string ppf "bool"
  | LongInt -> pp_print_string ppf "lint"
  | Void -> pp_print_string ppf "void"
  | Struct n ->
      pp_print_string ppf (if n < 0 then "struct" else Ain.ain.strt.(n).name)
  | Array _ as t ->
      pp_print_string ppf "array@";
      let base, rank = Type.array_base_and_rank t in
      pr_type ppf base;
      pr_array_rank ppf rank
  | Ref t ->
      pp_print_string ppf "ref ";
      pr_type ppf t
  | IMainSystem -> pp_print_string ppf "IMainSystem"
  | FuncType ftv -> (
      match Type.TypeVar.get_value ftv with
      | Id (n, _) -> pp_print_string ppf Ain.ain.fnct.(n).name
      | Type t ->
          (* Output the first functype matching the inferred type *)
          let ft =
            Array.find_exn Ain.ain.fnct ~f:(fun ft ->
                Poly.(t = Ain.FuncType.to_type ft))
          in
          pp_print_string ppf ft.name
      | Var ->
          Stdio.eprintf "Warning: unknown functype\n";
          pp_print_string ppf "functype")
  | StructMember _ -> failwith "cannot happen"
  | Delegate dtv -> (
      match Type.TypeVar.get_value dtv with
      | Id (n, _) -> pp_print_string ppf Ain.ain.delg.(n).name
      | Type t ->
          (* Output the first delegate type matching the inferred type *)
          let dt =
            Array.find_exn Ain.ain.delg ~f:(fun ft ->
                Poly.(t = Ain.FuncType.to_type ft))
          in
          pp_print_string ppf dt.name
      | Var ->
          Stdio.eprintf "Warning: unknown delegate type\n";
          pp_print_string ppf "delegate")
  | HllFunc2 -> pp_print_string ppf "hll_func2"
  | HllParam -> pp_print_string ppf "hll_param"

let pr_vartype ppf (arg : Ain.Variable.t) = fprintf ppf "%a" pr_type arg.type_

let pr_vardecl ppf (arg : Ain.Variable.t) =
  fprintf ppf "%a %s" pr_type arg.type_ arg.name

let pr_param_list pr_var ppf (params : Ain.Variable.t list) =
  let params =
    List.filter params ~f:(fun arg ->
        match arg.type_ with Void -> false | _ -> true)
  in
  pp_print_list ~pp_sep:comma pr_var ppf params

let print_function ppf (func : function_t) =
  let rec pr_lvalue prec ppf = function
    | NullRef -> pp_print_string ppf "NULL"
    | PageRef (StructPage, var) -> fprintf ppf "this.%s" var.name
    | PageRef (_, var) -> pp_print_string ppf var.name
    | RefRef lval -> pr_lvalue prec ppf lval
    | ArrayRef (array, index) ->
        fprintf ppf "%a[%a]"
          (pr_expr (prec_value PREC_DOT))
          array (pr_expr 0) index
    | MemberRef (obj, memb) ->
        fprintf ppf "%a.%s" (pr_expr (prec_value PREC_DOT)) obj memb.name
    | RefValue e -> pr_expr (prec_value PREC_DOT) ppf e
    | ObjRef _ as lval ->
        failwith ("pr_lvalue: unresolved ObjRef " ^ show_lvalue lval)
    | IncDec (fix, op, lval) ->
        let op = incdec_op op in
        open_paren prec op.prec ppf;
        (match fix with
        | Prefix -> fprintf ppf "%s%a" op.sym (pr_lvalue prec) lval
        | Postfix -> fprintf ppf "%a%s" (pr_lvalue prec) lval op.sym);
        close_paren prec op.prec ppf
  and pr_expr ?parent_op prec ppf = function
    | Number n -> fprintf ppf "%ld" n
    | Boolean b -> pp_print_string ppf (if b then "true" else "false")
    | Character c -> pr_char ppf (Int32.to_int_exn c)
    | Float x -> pp_print_string ppf (format_float x)
    | String s -> fprintf ppf "\"%s\"" (escape_dq s)
    | FuncAddr f -> fprintf ppf "&%s" f.name
    | MemberPointer (struc, slot) ->
        fprintf ppf "&%s::%s" Ain.ain.strt.(struc).name
          Ain.ain.strt.(struc).members.(slot).name
    | BoundMethod (Number -1l, f) ->
        fprintf ppf "&%s" (Ain.Function.parse_name f).name
    | BoundMethod (expr, f) ->
        fprintf ppf "&%a.%s"
          (pr_expr (prec_value PREC_DOT))
          expr (Ain.Function.parse_name f).name
    | Deref lval -> pr_lvalue prec ppf lval
    | DerefRef lval -> pr_lvalue prec ppf lval
    | New n -> fprintf ppf "new %s" Ain.ain.strt.(n).name
    | DerefStruct (_, expr) -> pr_expr prec ppf expr
    | Page StructPage -> pp_print_string ppf "this"
    | Null -> pp_print_string ppf "NULL"
    | Void -> pp_print_string ppf "<void>" (* FIXME *)
    | UnaryOp (FTOI, expr) -> fprintf ppf "int(%a)" (pr_expr 0) expr
    | UnaryOp (ITOF, expr) -> fprintf ppf "float(%a)" (pr_expr 0) expr
    | UnaryOp (ITOLI, expr) -> fprintf ppf "lint(%a)" (pr_expr 0) expr
    | UnaryOp (ITOB, Number 0l) -> pp_print_string ppf "false"
    | UnaryOp (ITOB, Number 1l) -> pp_print_string ppf "true"
    | UnaryOp (ITOB, expr) -> pr_expr prec ppf expr
    | UnaryOp (STOI, expr) ->
        fprintf ppf "%a.Int()" (pr_expr (prec_value PREC_DOT)) expr
    | UnaryOp (I_STRING, expr) -> fprintf ppf "string(%a)" (pr_expr 0) expr
    | UnaryOp (insn, expr) ->
        let op = operator insn in
        open_paren prec op.prec ppf;
        fprintf ppf "%s%a" op.sym (pr_expr op.rprec) expr;
        close_paren prec op.prec ppf
    | BinaryOp (insn, lhs, rhs) ->
        let op = operator insn in
        pr_binary_op parent_op prec op ppf lhs rhs
    | AssignOp (insn, lval, rhs) ->
        let op = operator insn in
        pr_binary_op parent_op prec op ppf (Deref lval) rhs
    | StringFormat (n, lhs, rhs) ->
        pr_binary_op parent_op prec (operator (S_MOD n)) ppf lhs rhs
    | TernaryOp (expr1, expr2, expr3) ->
        let op_prec = prec_value PREC_QUESTION in
        open_paren prec op_prec ppf;
        fprintf ppf "%a ? %a : %a"
          (pr_expr (op_prec + 1))
          expr1
          (pr_expr (op_prec + 1))
          expr2 (pr_expr op_prec) expr3;
        close_paren prec op_prec ppf
    | Call (f, args) -> fprintf ppf "%a(%a)" pr_callable f pr_arg_list args
    | C_Ref (str, i) ->
        fprintf ppf "%a[%a]" (pr_expr (prec_value PREC_DOT)) str (pr_expr 0) i
    | C_Assign (str, i, ch) ->
        pr_binary_op parent_op prec (operator ASSIGN) ppf (C_Ref (str, i)) ch
    | e ->
        eprintf "%a\n" pp_expr e;
        failwith "pr_expr: not implemented"
  and pr_binary_op parent_op prec op ppf lhs rhs =
    (* Match the AinDecompiler's parenthesizing rules. *)
    let prec' =
      match parent_op with
      | Some pop ->
          if prec = op.prec && not (String.equal pop.sym op.sym) then prec + 1
          else prec
      | None -> prec
    in
    let space = if String.equal op.sym "," then "" else " " in
    open_paren prec' op.prec ppf;
    fprintf ppf "%a%s%s %a"
      (pr_expr ~parent_op:op op.lprec)
      lhs space op.sym
      (pr_expr ~parent_op:op op.rprec)
      rhs;
    close_paren prec' op.prec ppf
  and pr_callable ppf = function
    | Function func -> pp_print_string ppf func.name
    | FuncPtr (_, e) -> pr_expr (prec_value PREC_DOT) ppf e
    | Delegate (_, e) -> pr_expr (prec_value PREC_DOT) ppf e
    | SysCall n -> pp_print_string ppf syscalls.(n).name
    | HllFunc (lib, func) -> fprintf ppf "%s.%s" lib func.name
    | Method (expr, func) ->
        fprintf ppf "%a.%s"
          (pr_expr (prec_value PREC_DOT))
          expr
          (strip_class_name func.name)
    | Builtin (insn, lval) ->
        fprintf ppf "%a.%s"
          (pr_lvalue (prec_value PREC_DOT))
          lval (builtin_method_name insn)
    | Builtin2 (insn, expr) ->
        fprintf ppf "%a.%s"
          (pr_expr (prec_value PREC_DOT))
          expr (builtin_method_name insn)
  and pr_arg_list ppf args = pp_print_list ~pp_sep:comma (pr_expr 0) ppf args in
  let pr_label ppf = function
    | Address label -> fprintf ppf "label%d:\n" label
    | CaseInt (_, k) -> fprintf ppf "case %ld:\n" k
    | CaseStr (_, s) -> fprintf ppf "case \"%s\":\n" (escape_dq s)
    | Default _ -> fprintf ppf "default:\n"
  in
  let rec pr_stmt indent in_else_if ppf = function
    | Block stmts ->
        print_indent indent ppf;
        pp_print_string ppf "{\n";
        pr_stmt_list (indent + 1) ppf (List.rev stmts);
        print_indent indent ppf;
        pp_print_string ppf "}\n"
    | Expression expr ->
        print_indent indent ppf;
        fprintf ppf "%a;\n" (pr_expr 0) expr
    | Return None ->
        print_indent indent ppf;
        pp_print_string ppf "return;\n"
    | Return (Some expr) ->
        print_indent indent ppf;
        fprintf ppf "return %a;\n" (pr_expr 0) expr
    | Break ->
        print_indent indent ppf;
        pp_print_string ppf "break;\n"
    | Continue ->
        print_indent indent ppf;
        pp_print_string ppf "continue;\n"
    | Goto (label, _) ->
        print_indent indent ppf;
        fprintf ppf "goto label%d;\n" label
    | VarDecl (var, None) ->
        print_indent indent ppf;
        fprintf ppf "%a;\n" pr_vardecl var
    | VarDecl (var, Some (_, Call (Builtin (A_ALLOC, _), dims))) ->
        print_indent indent ppf;
        fprintf ppf "%a%a;\n" pr_vardecl var pr_array_dims dims
    | VarDecl (var, Some (insn, e)) ->
        let op = operator insn in
        print_indent indent ppf;
        fprintf ppf "%a = %a;\n" pr_vardecl var
          (pr_expr ~parent_op:op op.rprec)
          e
    | IfElse (expr, stmt1, stmt2) -> (
        if not in_else_if then print_indent indent ppf;
        fprintf ppf "if (%a)\n" (pr_expr 0) expr;
        print_indent indent ppf;
        pp_print_string ppf "{\n";
        pr_stmt_list (indent + 1) ppf
          (match stmt1 with Block stmts -> List.rev stmts | stmt -> [ stmt ]);
        match stmt2 with
        | Block [] ->
            print_indent indent ppf;
            pp_print_string ppf "}\n"
        | IfElse _ ->
            print_indent indent ppf;
            pp_print_string ppf "}\n";
            print_indent indent ppf;
            pp_print_string ppf "else ";
            pr_stmt indent true ppf stmt2
        | _ ->
            print_indent indent ppf;
            pp_print_string ppf "}\n";
            print_indent indent ppf;
            pp_print_string ppf "else\n";
            print_indent indent ppf;
            pp_print_string ppf "{\n";
            pr_stmt_list (indent + 1) ppf
              (match stmt2 with
              | Block stmts -> List.rev stmts
              | stmt -> [ stmt ]);
            print_indent indent ppf;
            pp_print_string ppf "}\n")
    | Switch (_, expr, body) ->
        print_indent indent ppf;
        fprintf ppf "switch (%a)\n" (pr_expr 0) expr;
        print_indent indent ppf;
        pp_print_string ppf "{\n";
        pr_stmt_list (indent + 1) ppf
          (match body with Block stmts -> List.rev stmts | stmt -> [ stmt ]);
        print_indent indent ppf;
        pp_print_string ppf "}\n"
    | While (cond, body) ->
        print_indent indent ppf;
        fprintf ppf "while (%a)\n" (pr_expr 0) cond;
        print_indent indent ppf;
        pp_print_string ppf "{\n";
        pr_stmt_list (indent + 1) ppf
          (match body with Block stmts -> List.rev stmts | stmt -> [ stmt ]);
        print_indent indent ppf;
        pp_print_string ppf "}\n"
    | DoWhile (body, cond) ->
        print_indent indent ppf;
        pp_print_string ppf "do {\n";
        pr_stmt_list (indent + 1) ppf
          (match body with Block stmts -> List.rev stmts | stmt -> [ stmt ]);
        print_indent indent ppf;
        fprintf ppf "} while (%a);\n" (pr_expr 0) cond
    | For (init, cond, inc, body) ->
        print_indent indent ppf;
        pp_print_string ppf "for (";
        (match init with None -> () | Some e -> pr_expr 0 ppf e);
        pp_print_string ppf "; ";
        (match cond with None -> () | Some e -> pr_expr 0 ppf e);
        pp_print_string ppf "; ";
        (match inc with None -> () | Some e -> pr_expr 0 ppf e);
        fprintf ppf ")\n";
        print_indent indent ppf;
        pp_print_string ppf "{\n";
        pr_stmt_list (indent + 1) ppf
          (match body with Block stmts -> List.rev stmts | stmt -> [ stmt ]);
        print_indent indent ppf;
        pp_print_string ppf "}\n"
    | Label label ->
        print_indent (indent - 1) ppf;
        pr_label ppf label
    | Assert expr ->
        print_indent indent ppf;
        fprintf ppf "assert(%a);\n" (pr_expr 0) expr
    | ScenarioJump s ->
        print_indent indent ppf;
        fprintf ppf "jump %s;\n" s
    | Msg (s, Some (Call (f, []))) ->
        print_indent indent ppf;
        fprintf ppf "'%s' %a;\n" (escape_sq s) pr_callable f
    | Msg (s, Some e) ->
        print_indent indent ppf;
        fprintf ppf "'%s' %a;\n" (escape_sq s) (pr_expr 0) e
    | Msg (s, None) ->
        print_indent indent ppf;
        fprintf ppf "'%s';\n" (escape_sq s)
  and pr_stmt_list indent ppf stmts =
    pp_print_list ~pp_sep:(fun _ _ -> ()) (pr_stmt indent false) ppf stmts
  in
  let pr_func_signature ppf (func : function_t) =
    let return_type = func.func.return_type in
    (match func.struc with
    | Some (struc : Ain.Struct.t) ->
        if String.equal func.name "0" then
          fprintf ppf "%s::%s" struc.name struc.name
        else if String.equal func.name "1" then
          fprintf ppf "%s::~%s" struc.name struc.name
        else fprintf ppf "%a %s::%s" pr_type return_type struc.name func.name
    | None ->
        if func.func.is_label then fprintf ppf "#%s" func.name
        else fprintf ppf "%a %s" pr_type return_type func.name);
    fprintf ppf "(%a)\n" (pr_param_list pr_vardecl)
      (Ain.Function.args func.func)
  in
  pr_func_signature ppf func;
  let body =
    match func.body with Block _ -> func.body | stmt -> Block [ stmt ]
  in
  pr_stmt 0 false ppf body

let print_struct_decl ppf (struc : struct_t) =
  fprintf ppf "class %s\n{\npublic:\n" struc.struc.name;
  List.iter struc.members ~f:(fun v ->
      match v.v.type_ with
      | Void -> ()
      | _ ->
          print_indent 1 ppf;
          pr_vardecl ppf v.v;
          pr_array_dims ppf v.dims;
          pp_print_string ppf ";\n");
  if
    (not (Array.is_empty struc.struc.members))
    && not (List.is_empty struc.methods)
  then pp_print_string ppf "\n";
  List.iter struc.methods ~f:(fun func ->
      print_indent 1 ppf;
      if String.equal func.name "0" then fprintf ppf "%s" struc.struc.name
      else if String.equal func.name "1" then fprintf ppf "~%s" struc.struc.name
      else fprintf ppf "%a %s" pr_type func.func.return_type func.name;
      fprintf ppf "(%a);\n" (pr_param_list pr_vardecl)
        (Ain.Function.args func.func));
  pp_print_string ppf "};\n"

let print_functype_decl ppf keyword (ft : Ain.FuncType.t) =
  fprintf ppf "%s %a %s " keyword pr_type ft.return_type ft.name;
  match Ain.FuncType.args ft with
  | [] -> fprintf ppf "(void);\n"
  | args -> fprintf ppf "(%a);\n" (pr_param_list pr_vartype) args

let print_globals ppf (globals : variable list) =
  let groups =
    List.group globals ~break:(fun a b -> a.v.group_index <> b.v.group_index)
  in
  let print_group indent =
    List.iter ~f:(fun (v : variable) ->
        print_indent indent ppf;
        pr_vardecl ppf v.v;
        pr_array_dims ppf v.dims;
        pr_initval ppf v.v;
        pp_print_string ppf ";\n")
  in
  List.iter groups ~f:(fun group ->
      match (List.hd_exn group).v.group_index with
      | -1 -> print_group 0 group
      | gindex ->
          fprintf ppf "globalgroup %s\n{\n" Ain.ain.objg.(gindex);
          print_group 1 group;
          pp_print_string ppf "}\n")

let print_constants ppf =
  pp_print_string ppf "const int true = 1;\n";
  pp_print_string ppf "const int false = 0;\n\n"

let print_hll_function ppf (func : Ain.HLL.function_t) =
  fprintf ppf "%a %s" pr_type func.return_type func.name;
  match Ain.HLL.args func with
  | [] -> fprintf ppf "(void);\n"
  | args -> fprintf ppf "(%a);\n" (pr_param_list pr_vardecl) args

let print_hll_inc ppf =
  pp_print_string ppf "SystemSource = {\n";
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      fprintf ppf "\t\"%s.hll\",\t\"%s\",\n" hll.name hll.name);
  pp_print_string ppf "}\n"

let print_inc ppf srcs =
  pp_print_string ppf "Source = {\n";
  List.iter srcs ~f:(fun src -> fprintf ppf "\t\"%s\",\n" src);
  pp_print_string ppf "}\n"

type project_t = { name : string }

let print_pje ppf proj =
  pp_print_string ppf "// Project Environment File\n";
  fprintf ppf "ProjectName = \"%s\"\n" proj.name;
  pp_print_newline ppf ();
  fprintf ppf "CodeName = \"%s.ain\"\n" proj.name;
  pp_print_newline ppf ();
  fprintf ppf "#define _AINVERSION %d\n" Ain.ain.vers;
  fprintf ppf "#define _KEYCODE 0x%08lX\n" Ain.ain.keyc;
  fprintf ppf "#define _ISAI2FILE %B\n" Ain.ain.is_ai2;
  if Ain.ain.vers >= 6 then
    fprintf ppf "#define _USESMSG1 %B\n" (Option.is_some Ain.ain.msg1_uk);
  fprintf ppf "#define _OPTIMIZE_IFTHEN %B\n" Ain.ain.ifthen_optimized;
  pp_print_newline ppf ();
  fprintf ppf "GameVersion = %ld\n" Ain.ain.gver;
  pp_print_newline ppf ();
  pp_print_string ppf "// Settings for each directory\n";
  pp_print_string ppf "SourceDir = \".\"\n";
  pp_print_string ppf "HLLDir = \"HLL\"\n";
  pp_print_string ppf "ObjDir = \"OBJ\"\n";
  pp_print_string ppf "OutputDir = \"Run\"\n";
  pp_print_newline ppf ();
  pp_print_string ppf "Source = {\n";
  pp_print_string ppf "\t\"main.inc\",\n";
  pp_print_string ppf "}\n"
