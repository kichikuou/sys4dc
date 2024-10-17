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
open Instructions

let parse_method_name s =
  match String.lsplit2 s ~on:'@' with
  | None -> (None, s)
  | Some (left, name) -> (Hashtbl.find Ain.ain.struct_by_name left, name)

type function_bytecode = {
  func : Ain.Function.t;
  end_addr : int;
  code : (int * instruction) list;
  lambdas : function_bytecode list;
}

let rec parse_function func_id code =
  let lambdas = ref [] in
  let rec aux acc = function
    | (end_addr, ENDFUNC n) :: tl ->
        if n <> func_id then
          Printf.failwithf "Unexpected ENDFUNC %d at 0x%x (ENDFUNC %d expected)"
            n end_addr func_id ()
        else
          ( {
              func = Ain.ain.func.(func_id);
              end_addr;
              code = List.rev acc;
              lambdas = List.rev !lambdas;
            },
            tl )
    | (_, FUNC n) :: tl when Ain.ain.func.(n).is_lambda -> (
        let lambda, code = parse_function n tl in
        lambdas := lambda :: !lambdas;
        (* Remove JUMP over the lambda *)
        match (acc, code) with
        | (addr1, JUMP addr2) :: acc_tl, (addr2', insn) :: code_tl
          when addr2 = addr2' ->
            aux acc_tl ((addr1, insn) :: code_tl)
        | _, _ -> Printf.failwithf "No JUMP that skips %s" lambda.func.name ())
    | (end_addr, (FUNC _ | EOF _)) :: _ as code ->
        (* constructors are missing ENDFUNCs. *)
        ( {
            func = Ain.ain.func.(func_id);
            end_addr;
            code = List.rev acc;
            lambdas = List.rev !lambdas;
          },
          code )
    | hd :: tl -> aux (hd :: acc) tl
    | [] -> failwith "unexpected end of code section"
  in
  aux [] code

let parse_functions code =
  let rec aux acc = function
    | (_, FUNC func_id) :: tl ->
        let parsed, code = parse_function func_id tl in
        aux (parsed :: acc) code
    | [ (_, EOF _) ] -> List.rev acc
    | _ :: tl -> aux acc tl (* Junk code after EOF, ignore *)
    | [] -> failwith "unexpected end of code section"
  in
  aux [] code

let decompile_function (f : function_bytecode) =
  let struc, name = parse_method_name f.func.name in
  try
    let body =
      BasicBlock.create f.code f.end_addr f.func struc
      |> BasicBlock.generate_var_decls f.func
      |> ControlFlow.analyze
      |> TypeAnalysis.analyze_function f.func struc
      |> Transform.rename_labels |> Transform.recover_loop_initializer
      |> Transform.remove_array_initializer_call
      |> Transform.remove_implicit_array_free
      |> Transform.remove_generated_lockpeek
      |> Transform.remove_redundant_return
      |> Transform.remove_dummy_variable_assignment
      |> Transform.remove_vardecl_default_rhs
      |> Transform.fold_newline_func_to_msg
      |> Transform.remove_optional_arguments
      |> if Ain.ain.vers >= 6 then Transform.simplify_boolean_expr else Fn.id
    in
    CodeGen.{ func = f.func; struc; name; body }
  with e ->
    Stdio.eprintf "Error while decompiling function %s\n" f.func.name;
    raise e

let inspect_function (f : function_bytecode) =
  let struc, name = parse_method_name f.func.name in
  (BasicBlock.create f.code f.end_addr f.func struc
  |> (fun bbs ->
       Stdio.printf "BasicBlock representation:\n%s\n\n"
         ([%show: BasicBlock.t list] bbs);
       bbs)
  |> BasicBlock.generate_var_decls f.func
  |> ControlFlow.analyze
  |> (fun stmt ->
       Stdio.printf "\nAST representation:\n%s\n" (Ast.show_statement stmt);
       stmt)
  |> TypeAnalysis.analyze_function f.func struc
  |> Transform.rename_labels |> Transform.recover_loop_initializer
  |> Transform.remove_array_initializer_call
  |> Transform.remove_implicit_array_free |> Transform.remove_generated_lockpeek
  |> Transform.remove_redundant_return
  |> Transform.remove_dummy_variable_assignment
  |> Transform.remove_vardecl_default_rhs |> Transform.fold_newline_func_to_msg
  |> Transform.remove_optional_arguments
  |> if Ain.ain.vers >= 6 then Transform.simplify_boolean_expr else Fn.id)
  |> fun body ->
  Stdio.printf "\nDecompiled code:\n";
  CodeGen.(
    print_function Stdlib.Format.std_formatter
      { func = f.func; struc; name; body })

let group_by_source_file code =
  let rec aux acc curr = function
    | [] ->
        assert (List.is_empty curr);
        List.rev acc
    | ((_, EOF n) as hd) :: tl ->
        aux ((Ain.ain.fnam.(n), List.rev (hd :: curr)) :: acc) [] tl
    | hd :: tl -> aux acc (hd :: curr) tl
  in
  aux [] [] code

let to_variable_list vars =
  List.map (Array.to_list vars) ~f:(fun v -> CodeGen.{ v; dims = [] })

let extract_array_dims stmt vars =
  let h = Stdlib.Hashtbl.create (Array.length vars) in
  List.iter
    (match stmt with Ast.Block stmts -> stmts | _ -> [ stmt ])
    ~f:(function
      | Ast.Return _ -> ()
      | Expression (Call (Builtin (Instructions.A_ALLOC, PageRef (_, v)), dims))
        ->
          Stdlib.Hashtbl.add h v dims
      | _ -> failwith "unexpected statement in array initializer");
  List.map (Array.to_list vars) ~f:(fun v ->
      match Stdlib.Hashtbl.find_opt h v with
      | Some dims -> CodeGen.{ v; dims }
      | None -> { v; dims = [] })

(* In Ain v0, when a Function.t is a method, its name field contains the class
   name (the method name is not recorded anywhere). To simplify the
   decompilation process, rename them to align with the Ain v1+ naming
   convention. *)
let rename_ain_v0_methods () =
  if Ain.ain.vers = 0 then
    Array.iteri Ain.ain.func ~f:(fun i func ->
        match
          Array.find Ain.ain.strt ~f:(fun s -> String.equal s.name func.name)
        with
        | Some s when s.constructor = i ->
            func.name <- Printf.sprintf "%s@0" func.name
        | Some s when s.destructor = i ->
            func.name <- Printf.sprintf "%s@1" func.name
        | Some _ -> func.name <- Printf.sprintf "%s@method%d" func.name i
        | None -> ())

(* Ain v0 doesn't have FUNC/EOF instructions, so insert them *)
let rec insert_func acc next_fno = function
  | ((addr, _) as hd) :: tl
    when next_fno < Array.length Ain.ain.func
         && addr = Ain.ain.func.(next_fno).address ->
      insert_func (hd :: (addr, FUNC next_fno) :: acc) (next_fno + 1) tl
  | hd :: tl -> insert_func (hd :: acc) next_fno tl
  | [] -> List.rev ((-1, EOF 0) :: acc)

let preprocess_ain_v0 code =
  if Ain.ain.vers = 0 then (
    rename_ain_v0_methods ();
    Ain.ain.fnam <- [| "all.jaf" |];
    insert_func [] 0 code)
  else code

type decompiled_ain = {
  structs : CodeGen.struct_t array;
  globals : CodeGen.variable list;
  srcs : (string * CodeGen.function_t list) list;
}

let decompile () =
  let code = Instructions.decode Ain.ain.code in
  let code = preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let files = group_by_source_file code in
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          { struc; members = to_variable_list struc.members; methods = [] })
  in
  let globals = ref (to_variable_list Ain.ain.glob) in
  let srcs =
    List.map files ~f:(fun (fname, code_in_file) ->
        let funcs = parse_functions code_in_file in
        let decompiled_funcs = ref [] in
        let rec process_func func =
          let f = decompile_function func in
          (match f with
          | { struc = Some struc; _ } ->
              let s = structs.(struc.id) in
              if String.equal f.name "2" then
                s.members <- extract_array_dims f.body struc.members
              else (
                if not f.func.is_lambda then s.methods <- f :: s.methods;
                decompiled_funcs := f :: !decompiled_funcs)
          | { struc = None; name = "0"; _ } ->
              globals := extract_array_dims f.body Ain.ain.glob
          | { struc = None; name = "NULL"; _ } -> ()
          | _ -> decompiled_funcs := f :: !decompiled_funcs);
          List.iter func.lambdas ~f:process_func
        in
        List.iter funcs ~f:process_func;
        (fname, List.rev !decompiled_funcs))
  in
  Array.iter structs ~f:(fun s -> s.methods <- List.rev s.methods);
  { srcs; structs; globals = !globals }

let inspect funcname =
  let code = Instructions.decode Ain.ain.code in
  let code = preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let files = group_by_source_file code in
  match
    List.find_map files ~f:(fun (_, code_in_file) ->
        parse_functions code_in_file
        |> List.find ~f:(fun f -> String.equal f.func.name funcname))
  with
  | None -> failwith ("cannot find function " ^ funcname)
  | Some f -> inspect_function f

let export decompiled ain_name output_to_formatter =
  let sources = ref [] in
  let output_source fname f =
    sources := fname :: !sources;
    output_to_formatter fname f
  in
  output_source "constants.jaf" (fun ppf -> CodeGen.print_constants ppf);
  output_source "classes.jaf" (fun ppf ->
      Array.iter decompiled.structs ~f:(fun struc ->
          CodeGen.print_struct_decl ppf struc;
          Stdlib.Format.pp_print_string ppf "\n");
      Array.iter Ain.ain.fnct ~f:(fun ft ->
          CodeGen.print_functype_decl ppf "functype" ft);
      Array.iter Ain.ain.delg ~f:(fun ft ->
          CodeGen.print_functype_decl ppf "delegate" ft));
  output_source "globals.jaf" (fun ppf ->
      CodeGen.print_globals ppf decompiled.globals);
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      output_to_formatter
        ("HLL/" ^ hll.name ^ ".hll")
        (fun ppf ->
          Array.iter hll.functions ~f:(fun func ->
              CodeGen.print_hll_function ppf func)));
  output_source "HLL\\hll.inc" (fun ppf -> CodeGen.print_hll_inc ppf);
  List.iter decompiled.srcs ~f:(fun (fname, funcs) ->
      if not (List.is_empty funcs) then
        output_source fname (fun ppf ->
            List.iter funcs ~f:(fun func ->
                CodeGen.print_function ppf func;
                Stdlib.Format.pp_print_string ppf "\n")));
  output_to_formatter "main.inc" (fun ppf ->
      CodeGen.print_inc ppf (List.rev !sources));
  let project_name = Stdlib.Filename.remove_extension ain_name in
  output_to_formatter (project_name ^ ".pje") (fun ppf ->
      CodeGen.(print_pje ppf { name = project_name }))
