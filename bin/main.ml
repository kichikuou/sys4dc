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
open Sys4dc

let output_printer_getter out_dir_opt fname f =
  match out_dir_opt with
  | None ->
      let ppf = Format.std_formatter in
      Format.fprintf ppf "FILE %s\n\n" fname;
      f (CodeGen.create_printer ppf "")
  | Some out_dir ->
      let fname_components = String.split fname ~on:'\\' in
      let unix_fname = String.concat ~sep:"/" fname_components in
      let output_path = Filename.of_parts (out_dir :: fname_components) in
      Core_unix.mkdir_p (Filename.dirname output_path);
      let outc = Out_channel.create output_path in
      let ppf = Format.formatter_of_out_channel outc in
      f (CodeGen.create_printer ppf unix_fname);
      Format.pp_print_flush ppf ();
      Out_channel.close outc

let command =
  Command.basic ~summary:"Decompile an .ain file"
    (let%map_open.Command output_dir =
       flag "-o" (optional string) ~doc:"directory Output directory"
     and inspect_function =
       flag "-inspect" (optional string)
         ~doc:"function Inspect the decompilation process of a function"
     and print_addr = flag "-address" no_arg ~doc:" Print addresses"
     and ain_file = anon ("ain-file" %: string) in
     fun () ->
       Ain.load ain_file;
       match inspect_function with
       | None ->
           let decompiled = Decompile.decompile () in
           Decompile.export decompiled
             (Filename.basename ain_file)
             (output_printer_getter output_dir)
             ~print_addr
       | Some funcname -> Decompile.inspect funcname ~print_addr)

let () = Command_unix.run command
