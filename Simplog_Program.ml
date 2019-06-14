module S = Simplog_AST

type type_ =
  | ErrorType
  | BitsType of int
  | EnumType of string list
  | StructType of (type_ * string) array
  | IntType
  | BoolType

type expr = {
  e_kind : expr_kind;
  e_type : type_;
  e_loc : Lexing.position * Lexing.position
}

and expr_kind =
  | ErrorExpr
  | IntExpr of int
  | LitExpr of int option * radix * Z.t
  | BoolExpr of bool
  | IdentExpr of string
  | LetExpr of (string * expr) list * expr
  | StructExpr of expr array
  | UndefExpr
  | RangeSelectExpr of expr * int * int
  | BitSelectExpr of expr * int
  | FieldSelectExpr of expr * int
  | BinExpr of S.binop * expr * expr
  | CondExpr of expr * expr * expr
  | ApplyExpr of string * expr list
  | CaseExpr of expr * (expr list * expr) list
  | ConcatExpr of expr list
