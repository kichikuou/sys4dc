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
open Loc

let decompile_function (f : CodeSection.function_t) =
  try
    let body =
      BasicBlock.create f
      |> BasicBlock.generate_var_decls f.func
      |> ControlFlow.analyze
      |> TypeAnalysis.analyze_function f.func f.struc
      |> Transform.rename_labels |> Transform.recover_loop_initializer
      |> Transform.remove_array_initializer_call
      |> Transform.remove_implicit_array_free f.func.name
      |> Transform.remove_array_free_for_dead_arrays
      |> Transform.remove_generated_lockpeek
      |> Transform.remove_redundant_return
      |> Transform.remove_dummy_variable_assignment
      |> Transform.remove_vardecl_default_rhs
      |> Transform.fold_newline_func_to_msg
      |> Transform.remove_optional_arguments
      |> if Ain.ain.vers >= 6 then Transform.simplify_boolean_expr else Fn.id
    in
    CodeGen.{ func = f.func; struc = f.struc; name = f.name; body }
  with e ->
    Stdio.eprintf "Error while decompiling function %s\n" f.func.name;
    raise e

let inspect_function (f : CodeSection.function_t) ~print_addr =
  (BasicBlock.create f
  |> (fun bbs ->
       Stdio.printf "BasicBlock representation:\n%s\n\n"
         ([%show: BasicBlock.t list] bbs);
       bbs)
  |> BasicBlock.generate_var_decls f.func
  |> ControlFlow.analyze
  |> (fun stmt ->
       Stdio.printf "\nAST representation:\n%s\n"
         ([%show: Ast.statement loc] stmt);
       stmt)
  |> TypeAnalysis.analyze_function f.func f.struc
  |> Transform.rename_labels |> Transform.recover_loop_initializer
  |> Transform.remove_array_initializer_call
  |> Transform.remove_implicit_array_free f.func.name
  |> Transform.remove_array_free_for_dead_arrays
  |> Transform.remove_generated_lockpeek |> Transform.remove_redundant_return
  |> Transform.remove_dummy_variable_assignment
  |> Transform.remove_vardecl_default_rhs |> Transform.fold_newline_func_to_msg
  |> Transform.remove_optional_arguments
  |> if Ain.ain.vers >= 6 then Transform.simplify_boolean_expr else Fn.id)
  |> fun body ->
  Stdio.printf "\nDecompiled code:\n";
  CodeGen.(
    print_function ~print_addr
      (create_printer Stdio.stdout "")
      (create_debug_info ())
      { func = f.func; struc = f.struc; name = f.name; body })

let to_variable_list vars =
  List.map (Array.to_list vars) ~f:(fun v -> CodeGen.{ v; dims = [] })

let extract_array_dims stmt vars =
  let h = Stdlib.Hashtbl.create (Array.length vars) in
  if
    List.for_all
      (match stmt with { txt = Ast.Block stmts; _ } -> stmts | _ -> [ stmt ])
      ~f:(function
        | { txt = Ast.Return _; _ } -> true
        | {
            txt =
              Expression
                (Call (Builtin (Instructions.A_ALLOC, PageRef (_, v)), dims));
            _;
          } ->
            Stdlib.Hashtbl.add h v dims;
            true
        | _ -> false)
  then
    Some
      ( List.map (Array.to_list vars) ~f:(fun v ->
            match Stdlib.Hashtbl.find_opt h v with
            | Some dims -> CodeGen.{ v; dims }
            | None -> { v; dims = [] }),
        Stdlib.Hashtbl.length h > 0 )
  else None

let extract_array_dims_exn stmt vars =
  Option.value_exn
    (extract_array_dims stmt vars)
    ~message:"unexpected statement in array initializer"
  |> fst

type decompiled_ain = {
  structs : CodeGen.struct_t array;
  globals : CodeGen.variable list;
  srcs : (string * CodeGen.function_t list) list;
}

let decompile () =
  let code = Instructions.decode Ain.ain.code in
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let files = CodeSection.group_by_source_file code in
  let structs =
    Array.map Ain.ain.strt ~f:(fun struc ->
        CodeGen.
          { struc; members = to_variable_list struc.members; methods = [] })
  in
  let globals = ref (to_variable_list Ain.ain.glob) in
  let srcs =
    List.map files ~f:(fun (fname, code_in_file) ->
        let funcs = CodeSection.parse_functions code_in_file in
        let funcs =
          List.filter funcs ~f:(fun f ->
              not (CodeSection.is_overridden_function f))
        in
        let decompiled_funcs = ref [] in
        let rec process_func func =
          let f = decompile_function func in
          (match f with
          | { struc = Some struc; _ } ->
              let s = structs.(struc.id) in
              if String.equal f.name "2" then
                s.members <- extract_array_dims_exn f.body struc.members
              else if String.equal f.name "0" then (
                match extract_array_dims f.body struc.members with
                | Some (vs, true) -> s.members <- vs
                | _ ->
                    s.methods <- f :: s.methods;
                    decompiled_funcs := f :: !decompiled_funcs)
              else (
                if not f.func.is_lambda then s.methods <- f :: s.methods;
                decompiled_funcs := f :: !decompiled_funcs)
          | { struc = None; name = "0"; _ } ->
              globals := extract_array_dims_exn f.body Ain.ain.glob
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
  let code = CodeSection.preprocess_ain_v0 code in
  Ain.ain.ifthen_optimized <- Instructions.detect_ifthen_optimization code;
  let files = CodeSection.group_by_source_file code in
  match
    List.find_map files ~f:(fun (_, code_in_file) ->
        CodeSection.parse_functions code_in_file
        |> List.find ~f:(fun f -> String.equal f.CodeSection.func.name funcname))
  with
  | None -> failwith ("cannot find function " ^ funcname)
  | Some f -> inspect_function f

let export decompiled ain_name output_to_printer ~print_addr =
  let sources = ref [] in
  let output_source fname f =
    sources := fname :: !sources;
    output_to_printer fname f
  in
  let dbginfo = CodeGen.create_debug_info () in
  output_source "constants.jaf" (fun pr -> CodeGen.print_constants pr);
  output_source "classes.jaf" (fun pr ->
      Array.iter decompiled.structs ~f:(fun struc ->
          CodeGen.print_struct_decl pr struc;
          CodeGen.print_newline pr);
      Array.iter Ain.ain.fnct ~f:(fun ft ->
          CodeGen.print_functype_decl pr "functype" ft);
      Array.iter Ain.ain.delg ~f:(fun ft ->
          CodeGen.print_functype_decl pr "delegate" ft));
  output_source "globals.jaf" (fun pr ->
      CodeGen.print_globals pr decompiled.globals);
  Array.iter Ain.ain.hll0 ~f:(fun hll ->
      output_to_printer
        ("HLL/" ^ hll.name ^ ".hll")
        (fun pr ->
          Array.iter hll.functions ~f:(fun func ->
              CodeGen.print_hll_function pr func)));
  output_source "HLL\\hll.inc" (fun pr -> CodeGen.print_hll_inc pr);
  List.iter decompiled.srcs ~f:(fun (fname, funcs) ->
      if not (List.is_empty funcs) then
        output_source fname (fun pr ->
            List.iter funcs ~f:(fun func ->
                CodeGen.print_function ~print_addr pr dbginfo func;
                CodeGen.print_newline pr)));
  output_to_printer "main.inc" (fun pr ->
      CodeGen.print_inc pr (List.rev !sources));
  let project_name = Stdlib.Filename.remove_extension ain_name in
  output_to_printer (project_name ^ ".pje") (fun pr ->
      CodeGen.(print_pje pr { name = project_name }));
  output_to_printer "debug_info.json" (fun pr ->
      CodeGen.print_debug_info pr dbginfo)
