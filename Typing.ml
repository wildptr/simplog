open Simplog_AST
open ExtLib

module M = Map.Make(String)
module P = Simplog_Program

let error (loc : Lexing.position * Lexing.position) msg =
  let start_pos = fst loc in
  Printf.eprintf "%s:%d:%d: %s\n" start_pos.pos_fname start_pos.pos_lnum
    (start_pos.pos_cnum - start_pos.pos_bol) msg

type func = P.type_ * (P.type_ * string) list * expr

type env = {
  value_map : P.type_ option M.t;
  type_map : P.type_ M.t; (* for looking up type definitions *)
  func_map : func M.t;
  error : bool ref;
  mutable typed_decls : typed_decl list
}

let create_env () =
  { value_map = M.empty;
    type_map = M.empty;
    func_map = M.empty;
    error = ref false;
    typed_decls = [] }

exception Found of int

let the = Option.get

let extend_env env bindings =
  List.fold_left (fun env (name, value) -> M.add name value.e_type env)
    env bindings

let rec resolve_type env = function
  | TypeIdent (name, loc) ->
    begin
      try
        M.find name env.type_map
      with Not_found ->
        error loc (Printf.sprintf "undefined type ‘%s’" name);
        env.error := true;
        BoolType (* sorry... I mean error type *)
    end
  | BoolType ->
    P.BoolType
  | BitsType len ->
    P.BitsType len
  | TupleType types ->
    P.TupleType (List.map (resolve_type env) types)

let type_mismatch t1 t2 =
  match t1, t2 with
  | None, _ | _, None -> false
  | Some t1', Some t2' -> t1' <> t2'

let rec type_expr env (e : expr) =
  let err loc msg =
    error loc msg; env.error := true
  and sprintf = Printf.sprintf in
  let check_bounds i len loc =
    if not (i >= 0 && i < len) then
      err loc "index %d out of bounds";
  in
  match e.e_kind with
  | LitExpr (len, radix, value) ->
    e.e_type <- Some (P.BitsType len)
  | BoolExpr b ->
    e.e_type <- Some P.BoolType
  | IdentExpr name ->
    begin match M.find name env.value_map with
      | None -> () (* the value is defined but ill-typed *)
      | Some _ as t ->
        e.e_type <- t
      | exception Not_found ->
        err e.e_loc (sprintf "undefined identifier ‘%s’" name)
    end
  | LetExpr (bindings, body) ->
    List.iter (fun (name, value) -> type_expr env value) bindings;
    type_expr { env with value_map = extend_env env.value_map bindings } body
  | StructExpr (type_name, type_name_loc, fields) ->
    (* TODO: type checking of fields *)
    begin match M.find type_name env.type_map with
      | P.StructType (_, fields_exp) as typ ->
        let n = Array.length fields_exp in
        let f = Array.make n None in
        fields |> List.iter begin fun (f_name, f_name_loc, f_value) ->
          try
            for i=0 to n-1 do
              if snd fields_exp.(i) = f_name then raise (Found i)
            done;
            (* field not found *)
            err f_name_loc
              (sprintf "type ‘%s’ has no field named ‘%s’" type_name f_name);
          with Found i ->
          match f.(i) with
          | None ->
            f.(i) <- Some (type_expr env f_value)
          | Some _ ->
            err f_name_loc
              (sprintf "field ‘%s’ already defined" f_name);
        end;
        (* make sure all fields are defined *)
        for i=0 to n-1 do
          if f.(i) = None then begin
            err e.e_loc
              (sprintf "field ‘%s’ is undefined" (snd fields_exp.(i)))
          end
        done;
        e.e_type <- Some typ
      | _ ->
        err type_name_loc (sprintf "‘%s’ is not a struct type" type_name)
      | exception Not_found ->
        err type_name_loc (sprintf "undefined type ‘%s’" type_name)
    end
  | UndefExpr typ ->
    e.e_type <- Some (resolve_type env typ)
  | RangeSelectExpr (e1, hi, lo, index_loc) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some (BitsType len) ->
        check_bounds hi len index_loc;
        check_bounds lo len index_loc;
        if hi < lo then err index_loc "hi<lo"
      | Some _ ->
        err e1.e_loc "expression not of bits type"
    end;
    e.e_type <- Some (P.BitsType (hi-lo+1))
  | BitSelectExpr (e1, i, index_loc) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some (BitsType len) ->
        check_bounds i len index_loc
      | Some _ ->
        err e1.e_loc "expression not of bits type"
    end;
    e.e_type <- Some BoolType
  | FieldSelectExpr (e1, f_name, f_name_loc) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some typ ->
        begin match typ with
          | StructType (_, fields) ->
            begin
              try
                e.e_type <- Some (List.find_map (fun (typ, name) -> if name = f_name then Some typ else None) (Array.to_list fields))
              with Not_found ->
                err f_name_loc
                  (sprintf "expression has no field named ‘%s’" f_name)
            end
          | _ ->
            err e1.e_loc "expression not of struct type"
        end
    end
  | UnExpr (op, e1) ->
    type_expr env e1;
    let type_opt =
      match op with
      | Not ->
        begin match e1.e_type with
          | None -> None
          | Some BoolType as t -> t
          | Some _ ->
            err e.e_loc "type error";
            Some BoolType
        end
      | LogNot ->
        begin match e1.e_type with
          | None -> None
          | Some (BitsType _) as t -> t
          | Some _ ->
            err e.e_loc "type error";
            None
        end
    in
    e.e_type <- type_opt
  | BinExpr (op, e1, e2) ->
    type_expr env e1;
    type_expr env e2;
    let type_opt =
      match op with
      | Add | Sub | LogAnd | LogXor | LogOr ->
        begin match e1.e_type, e2.e_type with
          | None, _ | _, None -> ()
          | Some (P.BitsType len1), Some (P.BitsType len2) ->
            if len1 <> len2 then err e.e_loc "type mismatch"
          | _ ->
            err e.e_loc "type error"
        end;
        e2.e_type
      | SHL | LSHR | ASHR ->
        begin match e1.e_type, e2.e_type with
          | None, _ | _, None -> ()
          | Some (P.BitsType _), Some (P.BitsType _) -> ()
          | _ ->
            err e.e_loc "type error"
        end;
        e2.e_type
      | Eq | NotEq ->
        if type_mismatch e1.e_type e2.e_type then
          err e.e_loc "type mismatch";
        Some P.BoolType
      | SLT | ULT | SGE | UGE | SGT | UGT | SLE | ULE ->
        begin match e1.e_type, e2.e_type with
          | None, _ | _, None -> ()
          | Some (P.BitsType len1), Some (P.BitsType len2) ->
            if len1 <> len2 then
              err e.e_loc "length mismatch";
          | _ ->
            err e.e_loc "type error"
        end;
        Some P.BoolType
      | And | Or ->
        begin match e1.e_type, e2.e_type with
          | None, _ | _, None -> ()
          | Some P.BoolType, Some P.BoolType -> ()
          | _ ->
            err e.e_loc "type error"
        end;
        Some P.BoolType
    in
    e.e_type <- type_opt
  | CondExpr (e1, e2, e3) ->
    type_expr env e1;
    type_expr env e2;
    type_expr env e3;
    (* e1 should be of Bool type *)
    begin match e1.e_type with
      | None -> ()
      | Some BoolType -> ()
      | _ ->
        err e1.e_loc "expression not of Bool type"
    end;
    (* types of e2 and e3 should match *)
    if type_mismatch e2.e_type e3.e_type then
      err e.e_loc "type mismatch";
    e.e_type <- e2.e_type
  | ApplyExpr (func_name, args) ->
    List.iter (type_expr env) args;
    (* TODO: check arg types *)
    let ret_type_opt =
      match M.find func_name env.func_map with
      | (ret_type, _, _) -> Some ret_type
      | exception Not_found ->
        err e.e_loc (sprintf "undefined function ‘%s’" func_name);
        None
    in
    e.e_type <- ret_type_opt
  | CaseExpr (e1, branches) ->
    type_expr env e1;
    branches |> List.iter begin fun (cases, body) ->
      List.iter (type_expr env) cases;
      type_expr env body
    end;
    (* TODO *)
    begin match branches with
      | [] ->
        err e.e_loc "case expression has no branches"
      | branch1::_ ->
        e.e_type <- (snd branch1).e_type
    end
  | ConcatExpr es ->
    List.iter (type_expr env) es;
    let len =
      List.fold_left begin fun acc e ->
        match e.e_type with
        | None -> acc
        | Some (BitsType len) -> acc + len
        | _ -> err e.e_loc "type error"; acc
      end 0 es
    in
    e.e_type <- Some (P.BitsType len)
  | ReplicateExpr (n, e1) ->
    type_expr env e1;
    let len =
      match e1.e_type with
      | None -> 0
      | Some (BitsType len) -> len
      | _ -> err e1.e_loc "type error"; 0
    in
    e.e_type <- Some (BitsType (n*len))
  | TupleExpr es ->
    List.iter (type_expr env) es;
    begin
      try e.e_type <- Some (P.TupleType (List.map (fun e -> the e.e_type) es))
      with Option.No_value -> ()
    end

let extend_env_decl env = function
  | Typedef (typ, name) ->
    let typ' = resolve_type env typ in
    { env with type_map = M.add name typ' env.type_map }
  | Let (name, value) ->
    type_expr env value;
    env.typed_decls <- T_Let (name, value) :: env.typed_decls;
    { env with value_map = M.add name value.e_type env.value_map }
  | FuncDecl { name; ret_type; params; body } ->
    let ret_type' = resolve_type env ret_type
    and params' =
      params |>
      List.map (fun (typ, name) -> resolve_type env typ, name)
    in
    let body_env =
      { env with value_map = List.fold_left (fun m (typ, name) -> M.add name (Some typ) m) env.value_map params' }
    in
    type_expr body_env body;
    env.typed_decls <- T_FuncDecl { name; ret_type = ret_type'; params = params'; body } :: env.typed_decls;
    { env with func_map = M.add name (ret_type', params', body) env.func_map }
  | ModuleDecl _ ->
    (* TODO *)
    env
  | EnumDecl (type_name, variants) ->
    env.typed_decls <- T_EnumDecl (type_name, variants) :: env.typed_decls;
    let enum_type = P.EnumType (type_name, variants) in
    let value_map =
      List.fold_left (fun m variant -> M.add variant (Some enum_type) m)
        env.value_map variants
    in
    { env with value_map; type_map = M.add type_name enum_type env.type_map }
  | StructDecl (type_name, fields) ->
    let fields' =
      List.map (fun (typ, name) -> resolve_type env typ, name) fields
    in
    env.typed_decls <- T_StructDecl (type_name, fields') :: env.typed_decls;
    { env with type_map = M.add type_name (P.StructType (type_name, Array.of_list fields')) env.type_map }

let type_decls decls =
  let env = create_env () in
  let final_env = List.fold_left extend_env_decl env decls in
  List.rev final_env.typed_decls
