open Simplog_AST
open ExtLib
open Util

module M = Map.Make(String)
module P = Simplog_Program
module S = Set.Make(String)

let error (loc : Lexing.position * Lexing.position) msg =
  let start_pos, end_pos = loc in
  Printf.eprintf "%s:%d:%d-%d:%d: %s\n"
    start_pos.pos_fname
    start_pos.pos_lnum (start_pos.pos_cnum - start_pos.pos_bol)
    end_pos.pos_lnum (end_pos.pos_cnum - end_pos.pos_bol)
    msg

type func = P.type_ option * (P.type_ option * string) list * expr

type env = {
  value_map : P.type_ option M.t;
  type_map : P.type_ M.t; (* for looking up type definitions *)
  func_map : func M.t;
  module_map : module_info M.t;
  inst_map : module_info M.t;
  error : bool ref
}

let create_env () =
  { value_map = M.empty;
    type_map = M.empty;
    func_map = M.empty;
    module_map = M.empty;
    inst_map = M.empty;
    error = ref false }

exception Found of int
exception Error

let extend_env env bindings =
  List.fold_left (fun env (name, value) -> M.add name value.e_type env)
    env bindings

let rec resolve_type env = function
  | TypeIdent (name, loc) ->
    begin
      try Some (M.find name env.type_map)
      with Not_found ->
        error loc (sprintf "undefined type ‘%s’" name);
        env.error := true;
        None
    end
  | BoolType ->
    Some P.BoolType
  | BitsType len ->
    Some (P.BitsType len)
  | TupleType types ->
    let types_opt = List.map (resolve_type env) types in
    begin
      try Some (P.TupleType (List.map the types_opt))
      with Option.No_value -> None
    end
  | MapType (t1, t2) ->
    begin match resolve_type env t1, resolve_type env t2 with
      | Some t1', Some t2' ->
        Some (P.MapType (t1', t2'))
      | _ -> None
    end

let type_mismatch t1 t2 =
  match t1, t2 with
  | None, _ | _, None -> false
  | Some t1', Some t2' -> t1' <> t2'

let show_type = P.show_type

let expect_bits_type e =
  match e.e_type with
  | None -> ()
  | Some (P.BitsType _) -> ()
  | Some t ->
    error e.e_loc (sprintf "bits type expected, got %s" (show_type t))

let expect_bool_type e =
  match e.e_type with
  | None -> ()
  | Some P.BoolType -> ()
  | Some t ->
    error e.e_loc (sprintf "bool type expected, got %s" (show_type t))

let rec type_expr env (e : expr) =
  let err loc msg =
    error loc msg; env.error := true
  in
  let check_bounds i len loc =
    if not (i >= 0 && i < len) then
      err loc (sprintf "index %d out of bounds (0 to %d)" i (len-1));
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
        err e.e_loc (sprintf "undeclared identifier ‘%s’" name)
    end
  | LetExpr (bindings, body) ->
    List.iter (fun (name, value) -> type_expr env value) bindings;
    type_expr { env with value_map = extend_env env.value_map bindings } body
  | StructExpr (type_name, type_name_loc, fields) ->
    begin match M.find type_name env.type_map with
      | P.StructType (_, fields_exp) as typ ->
        let n = Array.length fields_exp in
        let f = Array.make n None in
        fields |> List.iter begin fun (f_name, f_name_loc, f_value) ->
          type_expr env f_value;
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
            f.(i) <- Some f_value
          | Some _ ->
            err f_name_loc
              (sprintf "field ‘%s’ already defined" f_name);
        end;
        (* make sure all fields are defined *)
        for i=0 to n-1 do
          match f.(i) with
          | None ->
            err e.e_loc
              (sprintf "field ‘%s’ is undefined" (snd fields_exp.(i)))
          | Some e ->
            begin match e.e_type with
              | None -> ()
              | Some t ->
                let exp_type = fst fields_exp.(i) in
                if t <> exp_type then
                  err e.e_loc
                    (sprintf "expected type %s, got %s" (show_type exp_type) (show_type t))
            end
        done;
        e.e_type <- Some typ
      | _ ->
        err type_name_loc (sprintf "‘%s’ is not a struct type" type_name)
      | exception Not_found ->
        err type_name_loc (sprintf "undefined type ‘%s’" type_name)
    end
  | UndefExpr typ ->
    e.e_type <- resolve_type env typ
  | RangeSelectExpr (e1, hi, lo, index_loc) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some (BitsType len) ->
        check_bounds hi len index_loc;
        check_bounds lo len index_loc;
        if hi < lo then err index_loc "hi<lo"
      | Some t ->
        err e1.e_loc (sprintf "bits type expected, got %s" (show_type t))
    end;
    e.e_type <- Some (P.BitsType (hi-lo+1))
  | BitSelectExpr (e1, i, index_loc) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some (BitsType len) ->
        check_bounds i len index_loc
      | Some t ->
        err e1.e_loc (sprintf "bits type expected, got %s" (show_type t))
    end;
    e.e_type <- Some BoolType
  | FieldSelectExpr (e1, f_name, f_name_loc) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some typ ->
        begin match typ with
          | StructType (type_name, fields) ->
            begin
              try
                e.e_type <- Some (List.find_map (fun (typ, name) -> if name = f_name then Some typ else None) (Array.to_list fields))
              with Not_found ->
                err f_name_loc
                  (sprintf "type %s has no field named ‘%s’" type_name f_name)
            end
          | t ->
            err e1.e_loc (sprintf "struct type expected, got %s" (show_type t))
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
          | Some t ->
            err e.e_loc (sprintf "bool type expected, got %s" (show_type t));
            Some BoolType
        end
      | LogNot ->
        begin match e1.e_type with
          | None -> None
          | Some (BitsType _) as t -> t
          | Some t ->
            err e.e_loc (sprintf "bits type expected, got %s" (show_type t));
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
            if len1 <> len2 then begin
              error e1.e_loc (sprintf "this expression is %d-bit-long" len1);
              error e2.e_loc (sprintf "while this expression is %d-bit-long" len2);
              env.error := true
            end
          | _ ->
            expect_bits_type e1;
            expect_bits_type e2;
            env.error := true
        end;
        e2.e_type
      | SHL | LSHR | ASHR ->
        begin match e1.e_type, e2.e_type with
          | None, _ | _, None -> ()
          | Some (P.BitsType _), Some (P.BitsType _) -> ()
          | _ ->
            expect_bits_type e1;
            expect_bits_type e2;
            env.error := true
        end;
        e1.e_type
      | Eq | NotEq ->
        if type_mismatch e1.e_type e2.e_type then begin
          error e1.e_loc
            (sprintf "this expression has type %s" (show_type (the e1.e_type)));
          error e2.e_loc
            (sprintf "while this expression has type %s" (show_type (the e2.e_type)));
          env.error := true
        end;
        Some P.BoolType
      | SLT | ULT | SGE | UGE | SGT | UGT | SLE | ULE ->
        begin match e1.e_type, e2.e_type with
          | None, _ | _, None -> ()
          | Some (P.BitsType len1), Some (P.BitsType len2) ->
            if len1 <> len2 then begin
              error e1.e_loc (sprintf "this expression is %d-bit-long" len1);
              error e2.e_loc (sprintf "while this expression is %d-bit-long" len2);
              env.error := true
            end
          | _ ->
            expect_bits_type e1;
            expect_bits_type e2;
            env.error := true
        end;
        Some P.BoolType
      | And | Or ->
        begin match e1.e_type, e2.e_type with
          | None, _ | _, None -> ()
          | Some P.BoolType, Some P.BoolType -> ()
          | _ ->
            expect_bool_type e1;
            expect_bool_type e2;
            env.error := true
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
      | Some t ->
        err e1.e_loc (sprintf "bool type expected, got %s" (show_type t));
    end;
    (* types of e2 and e3 should match *)
    if type_mismatch e2.e_type e3.e_type then begin
      error e2.e_loc
        (sprintf "this expression has type %s" (show_type (the e2.e_type)));
      error e3.e_loc
        (sprintf "while this expression has type %s" (show_type (the e3.e_type)));
      env.error := true
    end else e.e_type <- e2.e_type
  | ApplyExpr (func_name, args) ->
    List.iter (type_expr env) args;
    let ret_type_opt =
      match M.find func_name env.func_map with
      | (ret_type_opt, params, _) ->
        let n_arg = List.length args
        and n_arg_exp = List.length params in
        if n_arg <> n_arg_exp then
          err e.e_loc (sprintf "expected %d arguments, got %d" n_arg_exp n_arg)
        else
          List.iter2 begin fun arg (exp_type, _) ->
            if type_mismatch arg.e_type exp_type then
              err arg.e_loc
                (sprintf "expected type %s, got %s"
                   (show_type (the exp_type)) (show_type (the arg.e_type)))
          end args params;
        ret_type_opt
      | exception Not_found ->
        err e.e_loc (sprintf "undefined function ‘%s’" func_name);
        None
    in
    e.e_type <- ret_type_opt
  | CaseExpr (e1, branches) ->
    type_expr env e1;
    branches |> List.iter begin fun (labels_opt, body) ->
      Option.may (List.iter (type_expr env)) labels_opt;
      type_expr env body
    end;
    (* TODO *)
    begin match branches with
      | [] ->
        err e.e_loc "case expression has no branches"
      | branch1::_ ->
        let body_types = List.map (fun (_, body) -> body.e_type) branches in
        if not (List.mem None body_types) then begin
          let body_types = List.map the body_types in
          let exp_type = List.hd body_types in
          if List.for_all ((=) exp_type) body_types then
            e.e_type <- Some exp_type
          else begin
            err e.e_loc "type mismatch in case expression:";
            branches |> List.iter begin fun (_, body) ->
              error body.e_loc
                ("this expression has type " ^ (show_type (the body.e_type)))
            end
          end
        end
    end
  | ConcatExpr es ->
    List.iter (type_expr env) es;
    let ill_typed = ref false in
    let len =
      List.fold_left begin fun acc e ->
        match e.e_type with
        | None ->
          ill_typed := true;
          acc
        | Some (BitsType len) -> acc + len
        | Some t ->
          err e.e_loc (sprintf "bits type expected, got %s" (show_type t));
          ill_typed := true;
          acc
      end 0 es
    in
    if not !ill_typed then e.e_type <- Some (P.BitsType len)
  | ReplicateExpr (n, e1) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some (BitsType len) ->
        e.e_type <- Some (BitsType (n*len))
      | Some t ->
        err e1.e_loc (sprintf "bits type expected, got %s" (show_type t))
    end
  | TupleExpr es ->
    List.iter (type_expr env) es;
    begin
      try e.e_type <- Some (P.TupleType (List.map (fun e -> the e.e_type) es))
      with Option.No_value -> ()
    end
  | IndexExpr (e1, e2) ->
    type_expr env e1;
    type_expr env e2;
    begin match e1.e_type with
      | None -> ()
      | Some (P.MapType (t1, t2)) ->
        begin match e2.e_type with
          | None -> ()
          | Some t ->
            if t <> t1 then
              err e2.e_loc
                (sprintf "expected type %s, got %s" (show_type t1) (show_type t))
        end;
        e.e_type <- Some t2
      | Some t ->
        err e.e_loc (sprintf "maps type expected, got %s" (show_type t));
    end
  | UpdateExpr (e1, e2, e3) ->
    type_expr env e1;
    type_expr env e2;
    type_expr env e3;
    (* TODO *)
    e.e_type <- e1.e_type
  | ExtendExpr (sign, len, e1) ->
    type_expr env e1;
    begin match e1.e_type with
      | None -> ()
      | Some (P.BitsType e1_len) ->
        if e1_len > len then
          err e1.e_loc
            (sprintf "attempt to extend %d-bit-long expression to %d bits"
               e1_len len);
        e.e_type <- Some (P.BitsType len)
      | Some t ->
        err e1.e_loc (sprintf "bits type expected, got %s" (show_type t))
    end

let type_module_item env = function
  | InstItem (inst_name, (ports : (string * loc * expr) list), inst_loc) ->
    List.iter (fun (_, _, e) -> type_expr env e) ports;
    let mod_info = M.find inst_name env.inst_map in
    (* map port name to provided value *)
    let port_map =
      List.fold_left (fun m (name, _, value) -> M.add name value m)
        M.empty ports
    in
    (* TODO: ... *)
    let input_map =
      List.fold_left begin fun m (exp_type, port_name) ->
        match M.find port_name port_map with
        | e ->
          begin match e.e_type with
            | None -> ()
            | Some typ ->
              if typ <> exp_type then begin
                error e.e_loc
                  (sprintf "expected type %s, got %s"
                     (show_type exp_type) (show_type typ));
                env.error := true
              end
          end;
          M.add port_name e m
        | exception Not_found ->
          error inst_loc (sprintf "input port ‘%s’ is not connected" port_name);
          env.error := true;
          m
      end M.empty mod_info.inputs
    and output_map =
      List.fold_left begin fun m (exp_type, port_name) ->
        let defined_name_opt =
          match M.find_opt port_name port_map with
          | None -> None
          | Some e ->
            begin match e.e_type with
              | None -> ()
              | Some typ ->
                if typ <> exp_type then begin
                  error e.e_loc
                    (sprintf "expected type %s, got %s"
                       (show_type exp_type) (show_type typ));
                  env.error := true
                end
            end;
            (* make sure output is connected to an identifier *)
            begin match e.e_kind with
              | IdentExpr name -> Some name
              | _ ->
                error e.e_loc "invalid output connection";
                env.error := true;
                None
            end
        in
        M.add port_name defined_name_opt m
      end M.empty mod_info.outputs
    in
    let used_inputs_out =
      mod_info.inputs_used_by_out |>
      List.filter_map (fun (_, name) -> M.find_opt name input_map)
    and used_inputs_upd =
      mod_info.inputs_used_by_upd |>
      List.filter_map (fun (_, name) -> M.find_opt name input_map)
    in
    let defined_names =
      M.fold begin fun port_name defined_name_opt acc ->
        match defined_name_opt with
        | None -> acc
        | Some defined_name -> defined_name :: acc
      end output_map []
    in
    T_InstItem
      { name = inst_name; mod_info; input_map; output_map;
        used_inputs_out; used_inputs_upd; defined_names }
  | AssignItem (name, value) ->
    type_expr env value;
    T_AssignItem (name, value)
  | RegAssignItem (name, value, guard) ->
    type_expr env value;
    Option.may (type_expr env) guard;
    T_RegAssignItem (name, value, guard)

let type_module_decl env (md : module_decl) : module_info =
  let ports =
    List.map (fun (dir, typ, name) -> dir, resolve_type env typ, name) md.ports
  in
  let vals, regs, insts =
    let tmpv = ref []
    and tmpr = ref []
    and tmpi = ref [] in
    md.decls |> List.iter begin fun decl ->
      match decl with
      | ValDecl (typ, names) ->
        let typ' = resolve_type env typ in
        List.iter (fun name -> tmpv := (typ', name) :: !tmpv) names
      | RegDecl (typ, names) ->
        let typ' = resolve_type env typ in
        List.iter (fun name -> tmpr := (typ', name) :: !tmpr) names
      | InstDecl (mod_name, names) ->
        let mod_info = M.find mod_name env.module_map in
        List.iter (fun name -> tmpi := (mod_info, name) :: !tmpi) names
    end;
    List.rev !tmpv, List.rev !tmpr, List.rev !tmpi
  in

  (* extend environment with input & output ports *)
  let env =
    List.fold_left begin fun env (dir, typ, name) ->
      { env with value_map = M.add name typ env.value_map }
    end env ports
  in

  (* extend environment with value declarations *)
  let env =
    List.fold_left begin fun env (typ, name) ->
      { env with value_map = M.add name typ env.value_map }
    end env vals
  in

  (* ... with reg declarations *)
  let env =
    List.fold_left begin fun env (typ, name) ->
      { env with value_map = M.add name typ env.value_map }
    end env regs
  in

  (* ... with instance declarations *)
  let inst_map =
    List.fold_left (fun m (mod_info, inst_name) -> M.add inst_name mod_info m)
      M.empty insts
  in
  let env = { env with inst_map } in

  let typed_items = List.map (type_module_item env) md.items in

  (* compute module_info *)

  (* collect input and output ports *)
  let inputs =
    ports |> List.filter_map begin fun (dir, typ, name) ->
      if dir = Input then Some (the typ, name) else None
    end
  and outputs =
    ports |> List.filter_map begin fun (dir, typ, name) ->
      if dir = Output then Some (the typ, name) else None
    end
  in

  let module G = Graph.Imperative.Digraph.Concrete(String_Key) in

  let val_dep_graph = G.create () in

  typed_items |> List.iter begin function
    | T_AssignItem (name, value) ->
      G.add_vertex val_dep_graph name;
      visit_expr begin fun e ->
        match e.e_kind with
        | IdentExpr used_name ->
          (*Printf.eprintf "%s depends on %s\n" name used_name;*)
          G.add_edge val_dep_graph used_name name
        | _ -> ()
      end value
    | T_RegAssignItem (name, value, guard) ->
      let next_name = name ^ "'" in
      G.add_vertex val_dep_graph next_name;
      let visit e =
        match e.e_kind with
        | IdentExpr used_name ->
          (*Printf.eprintf "%s depends on %s\n" next_name used_name;*)
          G.add_edge val_dep_graph used_name next_name
        | _ -> ()
      in
      visit_expr visit value;
      Option.may (visit_expr visit) guard
    | T_InstItem inst ->
      let visit e =
        match e.e_kind with
        | IdentExpr used_name ->
          List.iter (G.add_edge val_dep_graph used_name) inst.defined_names
        | _ -> ()
      in
      List.iter (visit_expr visit) inst.used_inputs_out;
      List.iter (G.add_edge val_dep_graph inst.name) inst.defined_names;
      let next_state_name = inst.name ^ "'" in
      let visit e =
        match e.e_kind with
        | IdentExpr used_name ->
          G.add_edge val_dep_graph used_name next_state_name
        | _ -> ()
      in
      List.iter (visit_expr visit) inst.used_inputs_upd;
      G.add_edge val_dep_graph inst.name next_state_name
  end;

  let reg_names = List.map snd regs
  and inst_names = List.map snd insts in
  let used_names_out =
    let tmp = ref S.empty in
    let rec visit node =
      if not (S.mem node !tmp) then begin
        tmp := S.add node !tmp;
        G.iter_pred visit val_dep_graph node
      end
    in
    outputs |> List.iter (fun (_, name) -> visit name);
    !tmp
  and used_names_upd =
    let tmp = ref S.empty in
    let rec visit node =
      if not (S.mem node !tmp) then begin
        tmp := S.add node !tmp;
        G.iter_pred visit val_dep_graph node
      end
    in
    reg_names |> List.iter (fun name -> visit (name ^ "'"));
    inst_names |> List.iter (fun name -> visit (name ^ "'"));
    !tmp
  in

  let inputs_used_by_out =
    inputs |> List.filter (fun (_, name) -> S.mem name used_names_out)
  and inputs_used_by_upd =
    inputs |> List.filter (fun (_, name) -> S.mem name used_names_upd)
  in

  (*Format.eprintf "module %s\n  inputs used by out: %a\n  inputs used by upd: %a@." md.name
    (pp_comma_sep_list Format.pp_print_string) (List.map snd inputs_used_by_out)
    (pp_comma_sep_list Format.pp_print_string) (List.map snd inputs_used_by_upd);*)

  (*{ name = md.name; ports; state_elements; items = List.rev typed_items },*)
  { module_name = md.name; inputs_used_by_out; inputs_used_by_upd;
    used_names_out; used_names_upd;
    regs = List.map (fun (typ, name) -> the typ, name) regs; insts;
    inputs; outputs; items = typed_items;
    val_dep_graph; inst_map }

let extend_env_decl env = function
  | Typedef (typ, name) ->
    let env' =
      match resolve_type env typ with
      | None -> env
      | Some typ' ->
        { env with type_map = M.add name typ' env.type_map }
    in
    env', [] (* no typed decls *)
  | Let (name, value) ->
    type_expr env value;
    { env with value_map = M.add name value.e_type env.value_map },
    [T_Let (name, value)]
  | FuncDecl { name; ret_type; params; body } ->
    let ret_type' = resolve_type env ret_type
    and params' =
      List.map (fun (typ, name) -> resolve_type env typ, name) params
    in
    let body_env =
      { env with value_map = List.fold_left (fun m (typ, name) -> M.add name typ m) env.value_map params' }
    in
    type_expr body_env body;
    { env with func_map = M.add name (ret_type', params', body) env.func_map },
    [T_FuncDecl { name; ret_type = ret_type'; params = params'; body }]
  | ModuleDecl md ->
    let mod_info = type_module_decl env md in
    { env with module_map = M.add md.name mod_info env.module_map },
    [T_ModuleDecl mod_info]
  | EnumDecl (type_name, variants) ->
    let enum_type = P.EnumType (type_name, variants) in
    let value_map =
      List.fold_left (fun m variant -> M.add variant (Some enum_type) m)
        env.value_map variants
    in
    { env with value_map; type_map = M.add type_name enum_type env.type_map },
    [T_EnumDecl (type_name, variants)]
  | StructDecl (type_name, fields) ->
    let fields' =
      List.map (fun (typ, name) -> the (resolve_type env typ), name) fields
    in
    { env with type_map = M.add type_name (P.StructType (type_name, Array.of_list fields')) env.type_map },
    [T_StructDecl (type_name, fields')]

let type_decls decls =
  let env = create_env () in
  let env', decls' =
    List.fold_left begin fun (env, acc) decl ->
      let env', decls' = extend_env_decl env decl in
      env', decls' @ acc
    end (env, []) decls
  in if !(env'.error) then raise Error; env', List.rev decls'
