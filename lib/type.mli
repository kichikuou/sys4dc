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

module TypeVar : sig
  type 'a value = Var | Type of 'a | Id of int * 'a [@@deriving show]
  type 'a t [@@deriving show]

  val create : 'a value -> 'a t
  val get_value : 'a t -> 'a value
  val set_id : 'a t -> int -> 'a -> unit
  val set_type : 'a t -> 'a -> unit
  val unify : 'a t -> 'a t -> unit
end

type ain_type =
  | Any
  | Void
  | Int
  | Float
  | Char
  | String
  | Bool
  | LongInt
  | IMainSystem
  | Struct of int
  | Array of ain_type
  | Ref of ain_type
  | FuncType of func_type TypeVar.t
  | StructMember of int
  | Delegate of func_type TypeVar.t
  | HllFunc2
  | HllParam
[@@deriving show]

and func_type = { return_type : ain_type; arg_types : ain_type list }

val create : int -> struc:int -> rank:int -> ain_type
val create_ain11 : int -> struc:int -> subtype:ain_type option -> ain_type
val size_in_stack : ain_type -> int
val array_base_and_rank : ain_type -> ain_type * int
val replace_hll_param : ain_type -> ain_type -> ain_type
