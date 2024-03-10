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

let output_formatter_getter out_dir_opt fname f =
  match out_dir_opt with
  | None ->
      let ppf = Format.std_formatter in
      Format.fprintf ppf "FILE %s\n\n" fname;
      f ppf
  | Some out_dir ->
      let path = Filename.of_parts (out_dir :: String.split fname ~on:'\\') in
      Core_unix.mkdir_p (Filename.dirname path);
      let outc = Out_channel.create path in
      let ppf = Format.formatter_of_out_channel outc in
      f ppf;
      Format.pp_print_flush ppf ();
      Out_channel.close outc

let command =
  Command.basic ~summary:"Decompile an .ain file"
    (let%map_open.Command output_dir =
       flag "-o" (optional string) ~doc:"directory Output directory"
     and inspect_function =
       flag "-inspect" (optional string)
         ~doc:"function Inspect the decompilation process of a function"
     and ain_file = anon ("ain-file" %: string) in
     fun () ->
       Ain.load ain_file;
       match inspect_function with
       | None ->
           let decompiled = Decompile.decompile () in
           Decompile.export decompiled
             (Filename.basename ain_file)
             (output_formatter_getter output_dir)
       | Some funcname -> Decompile.inspect funcname)

let () = Command_unix.run command
