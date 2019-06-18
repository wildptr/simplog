open ExtLib
open Util

module S = Set.Make(String)
module H = Hashtbl.Make(String_Key)

type type_ =
  | BoolType
  | BitsType of int
  | EnumType of string * string list
  | StructType of string * (type_ * string) array
  | TupleType of type_ list
  | MapType of type_ * type_
  | AbsType of string

let rec pp_type f typ =
  let open Format in
  match typ with
  | BoolType ->
    pp_print_string f "bool"
  | BitsType len ->
    fprintf f "bits(%d)" len
  | EnumType (name, _)
  | StructType (name, _) ->
    pp_print_string f name
  | TupleType types ->
    fprintf f "(%a)" (pp_comma_sep_list pp_type) types
  | MapType (t1, t2) ->
    fprintf f "%a[%a]" pp_type t1 pp_type t2
  | AbsType name ->
    pp_print_string f name

let show_type typ =
  Format.asprintf "%a" pp_type typ
