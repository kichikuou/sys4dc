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
open Loc
open Type
open Ast
open Instructions

type variable = { v : Ain.Variable.t; dims : Ast.expr list }

type function_t = {
  func : Ain.Function.t;
  struc : Ain.Struct.t option;
  name : string;
  body : Ast.statement loc;
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

let pr_number ppf = function
  | Number n -> fprintf ppf "%ld" n
  | _ -> failwith "pr_number: non-number"

let pr_array_dims ?(pr_expr = pr_number) ppf dims =
  List.iter dims ~f:(fun e -> fprintf ppf "[%a]" pr_expr e)

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

and pr_arg_list ppf args = pp_print_list ~pp_sep:comma (pr_expr 0) ppf args

type debug_mapping = { addr : int; src : int; line : int }

type debug_info = {
  mutable sources : string list;
  mutable current_src : int;
  mutable mappings : debug_mapping list;
}

let create_debug_info () = { sources = []; current_src = -1; mappings = [] }

let add_debug_info dbginfo addr file line =
  let src =
    match dbginfo.sources with
    | s :: _ when String.equal s file -> dbginfo.current_src
    | _ ->
        dbginfo.sources <- file :: dbginfo.sources;
        dbginfo.current_src <- dbginfo.current_src + 1;
        dbginfo.current_src
  in
  (* If multiple lines are mapped to the same address, discard all but the last line *)
  dbginfo.mappings <-
    { addr; src; line }
    ::
    (match dbginfo.mappings with
    | hd :: tl when hd.addr = addr -> tl
    | _ -> dbginfo.mappings)

let debug_info_to_json dbginfo =
  let sources = List.rev_map dbginfo.sources ~f:(fun s -> `String s) in
  let mappings =
    List.rev_map dbginfo.mappings ~f:(fun { addr; src; line } ->
        `List [ `Int addr; `Int src; `Int line ])
  in
  `Assoc
    [
      ("version", `String "alpha-1");
      ("sources", `List sources);
      ("mappings", `List mappings);
    ]

type printer = { ppf : Format.formatter; file : string; mutable line : int }

let create_printer ppf file = { ppf; file; line = 1 }

let print_newline pr =
  pr.line <- pr.line + 1;
  pp_print_newline pr.ppf ()

let print_indent pr n = pp_print_string pr.ppf (String.make n '\t')
let println pr fmt = kfprintf (fun _ -> print_newline pr) pr.ppf fmt

let print_function ~print_addr pr dbginfo (func : function_t) =
  let addr_and_indent addr indent =
    if addr > 0 then add_debug_info dbginfo addr pr.file pr.line;
    if print_addr then fprintf pr.ppf "/* %08x */" addr;
    print_indent pr indent
  in
  let pr_label = function
    | Address label -> println pr "label%d:" label
    | CaseInt (_, k) -> println pr "case %ld:" k
    | CaseStr (_, s) -> println pr "case \"%s\":" (escape_dq s)
    | Default _ -> println pr "default:"
  in
  let rec print_stmt indent in_else_if stmt =
    match stmt.txt with
    | Block stmts ->
        addr_and_indent stmt.addr indent;
        println pr "{";
        print_stmt_list (indent + 1) (List.rev stmts);
        let end_addr =
          match stmts with [] -> stmt.end_addr | s :: _ -> s.end_addr
        in
        addr_and_indent end_addr indent;
        println pr "}"
    | Expression expr ->
        addr_and_indent stmt.addr indent;
        println pr "%a;" (pr_expr 0) expr
    | Return None ->
        addr_and_indent stmt.addr indent;
        println pr "return;"
    | Return (Some expr) ->
        addr_and_indent stmt.addr indent;
        println pr "return %a;" (pr_expr 0) expr
    | Break ->
        addr_and_indent stmt.addr indent;
        println pr "break;"
    | Continue ->
        addr_and_indent stmt.addr indent;
        println pr "continue;"
    | Goto (label, _) ->
        addr_and_indent stmt.addr indent;
        println pr "goto label%d;" label
    | VarDecl (var, None) ->
        addr_and_indent stmt.addr indent;
        println pr "%a;" pr_vardecl var
    | VarDecl (var, Some (_, Call (Builtin (A_ALLOC, _), dims))) ->
        addr_and_indent stmt.addr indent;
        println pr "%a%a;" pr_vardecl var
          (pr_array_dims ~pr_expr:(pr_expr 0))
          dims
    | VarDecl (var, Some (insn, e)) ->
        let op = operator insn in
        addr_and_indent stmt.addr indent;
        println pr "%a = %a;" pr_vardecl var (pr_expr ~parent_op:op op.rprec) e
    | IfElse (expr, stmt1, stmt2) -> (
        if not in_else_if then addr_and_indent stmt.addr indent;
        println pr "if (%a)" (pr_expr 0) expr;
        addr_and_indent stmt1.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match stmt1.txt with
          | Block stmts -> List.rev stmts
          | _ -> [ stmt1 ]);
        addr_and_indent stmt1.end_addr indent;
        println pr "}";
        match stmt2.txt with
        | Block [] -> ()
        | IfElse _ ->
            addr_and_indent stmt2.addr indent;
            pp_print_string pr.ppf "else ";
            print_stmt indent true stmt2
        | _ ->
            addr_and_indent stmt2.addr indent;
            println pr "else";
            addr_and_indent stmt2.addr indent;
            println pr "{";
            print_stmt_list (indent + 1)
              (match stmt2.txt with
              | Block stmts -> List.rev stmts
              | _ -> [ stmt2 ]);
            addr_and_indent stmt2.end_addr indent;
            println pr "}")
    | Switch (_, expr, body) ->
        addr_and_indent stmt.addr indent;
        println pr "switch (%a)" (pr_expr 0) expr;
        addr_and_indent body.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent body.end_addr indent;
        println pr "}"
    | While (cond, body) ->
        addr_and_indent stmt.addr indent;
        println pr "while (%a)" (pr_expr 0) cond;
        addr_and_indent body.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent body.end_addr indent;
        println pr "}"
    | DoWhile (body, cond) ->
        addr_and_indent stmt.addr indent;
        println pr "do {";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent cond.addr indent;
        println pr "} while (%a);" (pr_expr 0) cond.txt
    | For (init, cond, inc, body) ->
        addr_and_indent stmt.addr indent;
        pp_print_string pr.ppf "for (";
        (match init with None -> () | Some e -> pr_expr 0 pr.ppf e);
        pp_print_string pr.ppf "; ";
        (match cond with None -> () | Some e -> pr_expr 0 pr.ppf e);
        pp_print_string pr.ppf "; ";
        (match inc with None -> () | Some e -> pr_expr 0 pr.ppf e);
        println pr ")";
        addr_and_indent body.addr indent;
        println pr "{";
        print_stmt_list (indent + 1)
          (match body.txt with Block stmts -> List.rev stmts | _ -> [ body ]);
        addr_and_indent body.end_addr indent;
        println pr "}"
    | Label label ->
        addr_and_indent stmt.addr (indent - 1);
        pr_label label
    | Assert expr ->
        addr_and_indent stmt.addr indent;
        println pr "assert(%a);" (pr_expr 0) expr
    | ScenarioJump s ->
        addr_and_indent stmt.addr indent;
        println pr "jump %s;" s
    | Msg (s, Some (Call (f, []))) ->
        addr_and_indent stmt.addr indent;
        println pr "'%s' %a;" (escape_sq s) pr_callable f
    | Msg (s, Some e) ->
        addr_and_indent stmt.addr indent;
        println pr "'%s' %a;" (escape_sq s) (pr_expr 0) e
    | Msg (s, None) ->
        addr_and_indent stmt.addr indent;
        println pr "'%s';" (escape_sq s)
  and print_stmt_list indent stmts =
    List.iter stmts ~f:(fun stmt -> print_stmt indent false stmt)
  in
  let print_func_signature (func : function_t) =
    let return_type = func.func.return_type in
    (match func.struc with
    | Some (struc : Ain.Struct.t) ->
        if String.equal func.name "0" then
          fprintf pr.ppf "%s::%s" struc.name struc.name
        else if String.equal func.name "1" then
          fprintf pr.ppf "%s::~%s" struc.name struc.name
        else fprintf pr.ppf "%a %s::%s" pr_type return_type struc.name func.name
    | None ->
        if func.func.is_label then fprintf pr.ppf "#%s" func.name
        else fprintf pr.ppf "%a %s" pr_type return_type func.name);
    println pr "(%a)" (pr_param_list pr_vardecl) (Ain.Function.args func.func)
  in
  print_func_signature func;
  let body =
    match func.body.txt with
    | Block _ -> func.body
    | _ -> { func.body with txt = Block [ func.body ] }
  in
  print_stmt 0 false body

let print_struct_decl pr (struc : struct_t) =
  println pr "class %s" struc.struc.name;
  println pr "{";
  println pr "public:";
  List.iter struc.members ~f:(fun v ->
      match v.v.type_ with
      | Void -> ()
      | _ ->
          print_indent pr 1;
          pr_vardecl pr.ppf v.v;
          pr_array_dims pr.ppf v.dims;
          println pr ";");
  if
    (not (Array.is_empty struc.struc.members))
    && not (List.is_empty struc.methods)
  then print_newline pr;
  List.iter struc.methods ~f:(fun func ->
      print_indent pr 1;
      if String.equal func.name "0" then fprintf pr.ppf "%s" struc.struc.name
      else if String.equal func.name "1" then
        fprintf pr.ppf "~%s" struc.struc.name
      else fprintf pr.ppf "%a %s" pr_type func.func.return_type func.name;
      println pr "(%a);" (pr_param_list pr_vardecl)
        (Ain.Function.args func.func));
  println pr "};"

let print_functype_decl pr keyword (ft : Ain.FuncType.t) =
  fprintf pr.ppf "%s %a %s " keyword pr_type ft.return_type ft.name;
  match Ain.FuncType.args ft with
  | [] -> println pr "(void);"
  | args -> println pr "(%a);" (pr_param_list pr_vartype) args

let print_globals pr (globals : variable list) =
  let groups =
    List.group globals ~break:(fun a b -> a.v.group_index <> b.v.group_index)
  in
  let print_group indent =
    List.iter ~f:(fun (v : variable) ->
        print_indent pr indent;
        pr_vardecl pr.ppf v.v;
        pr_array_dims pr.ppf v.dims;
        pr_initval pr.ppf v.v;
        println pr ";")
  in
  List.iter groups ~f:(fun group ->
      match (List.hd_exn group).v.group_index with
      | -1 -> print_group 0 group
      | gindex ->
          println pr "globalgroup %s" Ain.ain.objg.(gindex);
          println pr "{";
          print_group 1 group;
          println pr "}")

let print_constants pr =
  println pr "const int true = 1;";
  println pr "const int false = 0;";
  print_newline pr

let print_hll_function pr (func : Ain.HLL.function_t) =
  fprintf pr.ppf "%a %s" pr_type func.return_type func.name;
  match Ain.HLL.args func with
  | [] -> println pr "(void);"
  | args -> println pr "(%a);" (pr_param_list pr_vardecl) args

let print_hll_inc pr =
  println pr "SystemSource = {";
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      println pr "\t\"%s.hll\",\t\"%s\"," hll.name hll.name);
  println pr "}"

let print_inc pr srcs =
  println pr "Source = {";
  List.iter srcs ~f:(fun src -> println pr "\t\"%s\"," src);
  println pr "}"

type project_t = { name : string }

let print_pje pr proj =
  println pr "// Project Environment File";
  println pr "ProjectName = \"%s\"" proj.name;
  print_newline pr;
  println pr "CodeName = \"%s.ain\"" proj.name;
  print_newline pr;
  println pr "#define _AINVERSION %d" Ain.ain.vers;
  println pr "#define _KEYCODE 0x%08lX" Ain.ain.keyc;
  println pr "#define _ISAI2FILE %B" Ain.ain.is_ai2;
  if Ain.ain.vers >= 6 then
    println pr "#define _USESMSG1 %B" (Option.is_some Ain.ain.msg1_uk);
  println pr "#define _OPTIMIZE_IFTHEN %B" Ain.ain.ifthen_optimized;
  print_newline pr;
  println pr "GameVersion = %ld" Ain.ain.gver;
  print_newline pr;
  println pr "// Settings for each directory";
  println pr "SourceDir = \".\"";
  println pr "HLLDir = \"HLL\"";
  println pr "ObjDir = \"OBJ\"";
  println pr "OutputDir = \"Run\"";
  print_newline pr;
  println pr "Source = {";
  println pr "\t\"main.inc\",";
  println pr "}"

let print_debug_info pr dbginfo =
  debug_info_to_json dbginfo |> Yojson.Basic.to_string |> pp_print_string pr.ppf
