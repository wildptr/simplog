type type_ =
  | BoolType
  | BitsType of int
  | EnumType of string * string list
  | StructType of string * (type_ * string) array
  | TupleType of type_ list
