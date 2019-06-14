type type_ =
  | TypeIdent of string * type_ list
  | BitsType of int
  | EnumType of string list
  | StructType of (type_ * string) list

type radix = Dec | Bin | Oct | Hex

type binop = Add | Sub | Eq | NotEq | LogAnd | LogXor | LogOr | And | Or

type expr =
  | IntExpr of int
  | LitExpr of int option * radix * Z.t
  | BoolExpr of bool
  | IdentExpr of string
  | LetExpr of (string * expr) list * expr
  | StructExpr of (string * expr) list
  | UndefExpr
  | RangeSelectExpr of expr * int * int
  | BitSelectExpr of expr * int
  | FieldSelectExpr of expr * string
  | BinExpr of binop * expr * expr
  | CondExpr of expr * expr * expr
  | ApplyExpr of string * expr list
  | CaseExpr of expr * (expr list * expr) list
  | ConcatExpr of expr list

type func_decl = {
  name : string;
  ret_type : type_;
  params : (type_ * string) list;
  body : expr
}

type port_direction = Input | Output

type inst_item = {
  mod_name : string;
  type_params : type_ list;
  inst_name : string;
  ports : (string * expr) list
}

type module_decl = {
  name : string;
  ports : (port_direction * type_ * string) list;
  items : module_item list
}

and decl =
  | Typedef of type_ * string
  | Import of string option * string list
  | Let of string * expr
  | FuncDecl of func_decl
  | ModuleDecl of module_decl

and module_item =
  | DeclItem of decl
  | ValItem of type_ * string list
  | InstItem of inst_item
  | AssignItem of string * expr
