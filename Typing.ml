module S = Simplog_AST
module P = Simplog_Program

open ExtLib

module M = Map.Make(String)

let error (loc : Lexing.position * Lexing.position) msg =
  let start_pos = fst loc in
  Printf.eprintf "%s:%d:%d: %s\n" start_pos.pos_fname start_pos.pos_lnum
    (start_pos.pos_cnum - start_pos.pos_bol) msg

let rec type_expr env tenv (e : S.expr) =
  let e_kind, e_type =
  match e.e_kind with
  | S.IntExpr n ->
    P.IntExpr n, P.IntType
  | S.LitExpr (None, radix, value) ->
    P.IntExpr (None, radix, value), P.IntType
  | S.LitExpr (Some len, radix, value) ->
    P.IntExpr (None, radix, value), P.BitsType len
  | S.BoolExpr b ->
    P.BoolExpr b, P.BoolType
  | S.IdentExpr name ->
    begin match M.find name env with
      | typ ->
        P.IdentExpr name, typ
      | exception Not_found ->
        error e.e_loc "undefined identifier";
        P.IdentExpr name, P.ErrorType
    end
  | S.LetExpr (bindings, body) ->
    let bindings' =
      List.map (fun (name, value) -> name, type_expr env tenv value) bindings
    in
    let body' = type_expr (extend_env env bindings') tenv body in
    P.LetExpr (bindings, body')
  | S.StructExpr (type_name, fields) ->
    begin match M.find type_name tenv with
      | P.StructType _ as typ ->
        _ (* TOOD *)
        P.StructExpr _, typ
      | _ ->
        error e.e_loc "not a struct type";
        P.ErrorExpr, P.ErrorType
      | exception Not_found ->
        error e.e_loc "undefined type";
        P.ErrorExpr, P.ErrorType
    end
