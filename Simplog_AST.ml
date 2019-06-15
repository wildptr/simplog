module P = Simplog_Program

type loc = Lexing.position * Lexing.position

type type_ =
  | TypeIdent of string * loc
  | BoolType
  | BitsType of int
  | TupleType of type_ list

type radix = Dec | Bin | Oct | Hex

type unop = LogNot | Not

type binop =
  | Add | Sub | Eq | NotEq | LogAnd | LogXor | LogOr | And | Or
  | SLT | ULT | SGE | UGE | SGT | UGT | SLE | ULE
  | SHL | LSHR | ASHR

type expr = {
  e_kind : expr_kind;
  mutable e_type : P.type_ option;
  e_loc : loc
}

and field = string * loc * expr

and expr_kind =
(*| IntExpr of int*)
  | LitExpr of int * radix * Z.t
  | BoolExpr of bool
  | IdentExpr of string
  | LetExpr of (string * expr) list * expr
  | StructExpr of string * loc * field list
  | UndefExpr of type_
  | RangeSelectExpr of expr * int * int * loc
  | BitSelectExpr of expr * int * loc
  | FieldSelectExpr of expr * string * loc
  | UnExpr of unop * expr
  | BinExpr of binop * expr * expr
  | CondExpr of expr * expr * expr
  | ApplyExpr of string * expr list
  | CaseExpr of expr * (expr list * expr) list
  | ConcatExpr of expr list
  | ReplicateExpr of int * expr
  | TupleExpr of expr list

type 't func_decl = {
  name : string;
  ret_type : 't;
  params : ('t * string) list;
  body : expr
}

type port_direction = Input | Output

type inst_item = {
  mod_name : string;
  type_params : type_ list;
  inst_name : string;
  ports : field list
}

type import = string option * string list

type 't module_decl = {
  name : string;
  ports : (port_direction * 't * string) list;
  items : module_item list
}

and decl =
  | Typedef of type_ * string
  | Let of string * expr
  | FuncDecl of type_ func_decl
  | ModuleDecl of type_ module_decl
  | EnumDecl of string * string list
  | StructDecl of string * (type_ * string) list

and module_item =
  | DeclItem of decl
  | ValItem of type_ * string list
  | InstItem of inst_item
  | AssignItem of string * expr

type typed_decl =
  | T_Let of string * expr
  | T_FuncDecl of P.type_ func_decl
  | T_ModuleDecl of P.type_ module_decl
  | T_EnumDecl of string * string list
  | T_StructDecl of string * (P.type_ * string) list
