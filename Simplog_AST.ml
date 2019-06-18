open ExtLib
open Util

module P = Simplog_Program
module S = Set.Make(String)
module H = Hashtbl.Make(String_Key)
module M = Map.Make(String)

type loc = Lexing.position * Lexing.position

type type_ =
  | TypeIdent of string * loc
  | BoolType
  | BitsType of int
  | TupleType of type_ list
  | MapType of type_ * type_

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
  | UndefExpr of type_
  | LetExpr of (string * expr) list * expr
  | StructExpr of string * loc * field list
  | RangeSelectExpr of expr * int * int * loc
  | BitSelectExpr of expr * int * loc
  | FieldSelectExpr of expr * string * loc
  | UnExpr of unop * expr
  | BinExpr of binop * expr * expr
  | CondExpr of expr * expr * expr
  | ApplyExpr of string * expr list
  | CaseExpr of expr * (expr list option * expr) list
  | ConcatExpr of expr list
  | ReplicateExpr of int * expr
  | TupleExpr of expr list
  | IndexExpr of expr * expr
  | UpdateExpr of expr * expr * expr
  | ExtendExpr of bool * int * expr

type 't func_decl = {
  name : string;
  ret_type : 't;
  params : ('t * string) list;
  body : expr
}

type port_direction = Input | Output

type import = string option * string list

type module_comp_decl =
  | ValDecl of type_ * string list
  | RegDecl of type_ * string list
  | InstDecl of string * string list

type module_item =
  | InstItem of string * field list (* inst_name, ports *) * loc
  | AssignItem of string * loc * expr
  | RegAssignItem of string * loc * expr * expr option (* r <= e [when g] *)

type module_decl = {
  name : string;
  ports : (port_direction * type_ * string) list;
  decls : module_comp_decl list;
  items : module_item list
}

type decl =
  | Typedef of type_ * string
  | Let of string * expr
  | FuncDecl of type_ func_decl
  | ModuleDecl of module_decl
  | EnumDecl of string * string list
  | StructDecl of string * (type_ * string) list

module G = Graph.Imperative.Digraph.Concrete(String_Key)

type inst_info = {
  name : string;
  mod_info : module_info;
  input_map : expr M.t;
  (* an output port may be unconnected, thus "option" *)
  output_map : string option M.t;
  used_inputs_out : expr list M.t;
  used_inputs_upd : expr list;
  defined_names : string list
}

and typed_module_item =
  | T_InstItem of inst_info
  | T_AssignItem of string * expr
  | T_RegAssignItem of string * expr * expr option

and module_info = {
  module_name : string;
  inputs : (P.type_ * string) list;
  outputs : (P.type_ * string) list;
  regs : (P.type_ * string) list;
  insts : (module_info * string) list;
  items : typed_module_item list;
  inputs_used_by_out : (P.type_ * string) list M.t;
  inputs_used_by_upd : (P.type_ * string) list;
  used_names_out : S.t M.t;
  used_names_upd : S.t;
  val_dep_graph : G.t;
  inst_map : module_info M.t
}

type typed_decl =
  | T_Let of string * expr
  | T_FuncDecl of P.type_ option func_decl
  | T_ModuleDecl of module_info
  | T_EnumDecl of string * string list
  | T_StructDecl of string * (P.type_ * string) list

let length_of_bits_expr e =
  match e.e_type with
  | Some (P.BitsType len) -> len
  | _ -> failwith "length_of_bits_expr"

let get_struct_name e =
  match e.e_type with
  | Some (P.StructType (name, _)) -> name
  | _ -> failwith "get_struct_name"

let rec visit_expr f e =
  f e;
  match e.e_kind with
  | LitExpr _ | BoolExpr _ | IdentExpr _ | UndefExpr _ -> ()
  | LetExpr (bindings, body) ->
    List.iter (fun (name, value) -> visit_expr f value) bindings;
    visit_expr f body
  | StructExpr (_, _, fields) ->
    List.iter (fun (_, _, e1) -> visit_expr f e1) fields
  | RangeSelectExpr (e1, _, _, _)
  | BitSelectExpr (e1, _, _)
  | FieldSelectExpr (e1, _, _)
  | UnExpr (_, e1)
  | ReplicateExpr (_, e1)
  | ExtendExpr (_, _, e1) ->
    visit_expr f e1
  | BinExpr (_, e1, e2)
  | IndexExpr (e1, e2) ->
    visit_expr f e1;
    visit_expr f e2
  | CondExpr (e1, e2, e3)
  | UpdateExpr (e1, e2, e3) ->
    visit_expr f e1;
    visit_expr f e2;
    visit_expr f e3
  | ApplyExpr (_, es)
  | ConcatExpr es
  | TupleExpr es ->
    List.iter (visit_expr f) es
  | CaseExpr (e1, branches) ->
    visit_expr f e1;
    List.iter begin fun (labels_opt, body) ->
      Option.may (List.iter (visit_expr f)) labels_opt;
      visit_expr f body
    end branches
