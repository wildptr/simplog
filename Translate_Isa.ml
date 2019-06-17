open Simplog_AST
open ExtLib
open Util

open Format

module P = Simplog_Program
module H = Hashtbl.Make(String_Key)
module S = Set.Make(String)
module M = Map.Make(String)

let rec pp_type f = function
  | P.BoolType -> pp_print_string f "bool"
  | P.BitsType len -> fprintf f "%d word" len
  | P.EnumType (name, _) | P.StructType (name, _) ->
    pp_print_string f name
  | P.TupleType types -> pp_tuple_type f types
  | P.MapType (t1, t2) ->
    fprintf f "(%a \\<Rightarrow> %a)" pp_type t1 pp_type t2

and pp_tuple_type f types =
  if types = [] then
    pp_print_string f "unit"
  else
    pp_sep_list " \\<times> " pp_type f types

let reorder_fields fields fields_def =
  let n = Array.length fields_def in
  let result = Array.make n (List.hd fields) in
  for i=0 to n-1 do
    let field_name = snd fields_def.(i) in
    result.(i) <- List.find (fun (name, _, value) -> name = field_name) fields
  done;
  Array.to_list result

let rec pp_expr f e =
  match e.e_kind with
  | LitExpr (len, _, value) ->
    fprintf f "(%a :: %d word)" Z.pp_print value len
  | BoolExpr true ->
    pp_print_string f "True"
  | BoolExpr false ->
    pp_print_string f "False"
  | IdentExpr s ->
    pp_print_string f s
  | LetExpr (bindings, body) ->
    fprintf f "(case (%a) of (%a) \\<Rightarrow> %a)"
      (pp_comma_sep_list pp_expr) (List.map snd bindings)
      (pp_comma_sep_list pp_print_string) (List.map fst bindings)
      pp_expr body
  | StructExpr (_, _, fields) ->
    pp_print_string f "\\<lparr> ";
    let [@warning "-8"] Some (P.StructType (struct_name, fields_def)) = e.e_type in
    (pp_comma_sep_list (pp_field struct_name) f) (reorder_fields fields fields_def);
    pp_print_string f " \\<rparr>"
  | ApplyExpr (func_name, args) ->
    pp_print_char f '(';
    pp_print_string f func_name;
    List.iter (fprintf f " %a" pp_expr) args;
    pp_print_char f ')'
  | CaseExpr (e1, branches) ->
    begin match the e1.e_type with
      | P.BoolType | P.EnumType _ ->
        let default = ref None
        and l = ref [] in (* non-default cases, one label per case *)
        branches |> List.iter begin fun (labels_opt, body) ->
          match labels_opt with
          | None -> default := Some body
          | Some labels ->
            List.iter (fun label -> l := (label, body) :: !l) labels
        end;
        let default = !default and l = List.rev !l in
        if l = [] then begin (* the only case is the default case *)
          pp_expr f (the default)
        end else begin
          fprintf f "(case %a of %a" pp_expr e1 (pp_sep_list " | " pp_case_branch) l; begin match default with
            | None -> pp_print_char f ')'
            | Some default_value ->
              fprintf f " | _ \\<Rightarrow> %a)" pp_expr default_value
          end
        end
      | P.BitsType _ ->
        let default = ref "undefined"
        and l = ref [] in
        branches |> List.iter begin fun (labels_opt, body) ->
          match labels_opt with
          | None -> default := show_expr body
          | Some labels -> l := (labels, body) :: !l
        end;
        let default = !default and l = List.rev !l in
        (* "if %a = %a then %a else if %a = %a then %a else undefined" *)
        fprintf f "(if %a else %s)" (pp_sep_list " else if " (pp_case_branch' e1)) l default
      | _ -> assert false
    end
  | UnExpr (op, e1) ->
    begin match op with
      | LogNot -> fprintf f "(NOT %a)" pp_expr e1
      | Not    -> fprintf f "(\\<not> %a)" pp_expr e1
    end
  | BinExpr (op, e1, e2) ->
    begin match op with
      | Add    -> fprintf f "(%a + %a)" pp_expr e1 pp_expr e2
      | Sub    -> fprintf f "(%a - %a)" pp_expr e1 pp_expr e2
      | LogAnd -> fprintf f "(%a AND %a)" pp_expr e1 pp_expr e2
      | LogXor -> fprintf f "(%a XOR %a)" pp_expr e1 pp_expr e2
      | LogOr  -> fprintf f "(%a OR %a)" pp_expr e1 pp_expr e2
      | SHL    -> fprintf f "(%a << unat %a)" pp_expr e1 pp_expr e2
      | LSHR   -> fprintf f "(%a >> unat %a)" pp_expr e1 pp_expr e2
      | ASHR   -> fprintf f "(%a >>> unat %a)" pp_expr e1 pp_expr e2
      | Eq     -> fprintf f "(%a = %a)" pp_expr e1 pp_expr e2
      | NotEq  -> fprintf f "(%a \\<noteq> %a)" pp_expr e1 pp_expr e2
      | And    -> fprintf f "(%a \\<and> %a)" pp_expr e1 pp_expr e2
      | Or     -> fprintf f "(%a \\<or> %a)" pp_expr e1 pp_expr e2
      | ULT    -> fprintf f "(%a < %a)" pp_expr e1 pp_expr e2
      | UGE    -> fprintf f "(%a \\<ge> %a)" pp_expr e1 pp_expr e2
      | UGT    -> fprintf f "(%a > %a)" pp_expr e1 pp_expr e2
      | ULE    -> fprintf f "(%a \\<le> %a)" pp_expr e1 pp_expr e2
      | SLT    -> fprintf f "(sint %a < sint %a)" pp_expr e1 pp_expr e2
      | SGE    -> fprintf f "(sint %a \\<ge> sint %a)" pp_expr e1 pp_expr e2
      | SGT    -> fprintf f "(sint %a > sint %a)" pp_expr e1 pp_expr e2
      | SLE    -> fprintf f "(sint %a \\<le> sint %a)" pp_expr e1 pp_expr e2
    end
  | CondExpr (e1, e2, e3) ->
    fprintf f "(if %a then %a else %a)" pp_expr e1 pp_expr e2 pp_expr e3
  | UndefExpr _ ->
    fprintf f "(undefined :: %a)" pp_type (the e.e_type)
  | RangeSelectExpr (e1, hi, lo, _) ->
    fprintf f "(slice %d %a :: %d word)" lo pp_expr e1 (hi+1-lo)
  | BitSelectExpr (e1, i, _) ->
    fprintf f "(%a !! %d)" pp_expr e1 i
  | FieldSelectExpr (e1, field_name, _) ->
    assert (e1.e_type <> None);
    let struct_name = get_struct_name e1 in
    fprintf f "(%s_%s %a)" struct_name field_name pp_expr e1
  | TupleExpr es ->
    fprintf f "(%a)" (pp_comma_sep_list pp_expr) es
  | ConcatExpr es ->
    (* cannot use word_rcat, because it requires every operand to be of the
       same length *)
    (* "(word_cat e1 (word_cat e2 (word_cat e3 e4 :: n2 word) :: n1 word) :: n0 word)" *)
    (* n2 = len4 + len3
       n1 = len4 + len3 + len2
       n0 = len4 + len3 + len2 + len1 *)
    let len = length_of_bits_expr e in
    let rec pp acc f = function
      | [] -> assert false
      | [e1] -> pp_expr f e1
      | e1::es' ->
        fprintf f "(word_cat %a %a :: %d word)"
          pp_expr e1 (pp (acc - length_of_bits_expr e1)) es' acc
    in
    pp len f es
  | ReplicateExpr (n, e1) ->
    pp_print_string f "(word_rcat [";
    for i=0 to n-1 do
      if i>0 then pp_print_string f ", ";
      pp_expr f e1;
    done;
    fprintf f "] :: %d word)" (length_of_bits_expr e)
  | IndexExpr (e1, e2) ->
    fprintf f "(%a %a)" pp_expr e1 pp_expr e2
  | UpdateExpr (e1, e2, e3) ->
    fprintf f "(%a(%a := %a))" pp_expr e1 pp_expr e2 pp_expr e3
  | ExtendExpr (sign, len, e1) ->
    let op = if sign then "scast" else "ucast" in
    fprintf f "(%s %a :: %d word)" op pp_expr e1 len

and pp_field struct_name f (field_name, _, value) =
  fprintf f "%s_%s = %a" struct_name field_name pp_expr value

and pp_case_branch f (label, body) =
  fprintf f "%a \\<Rightarrow> %a" pp_expr label pp_expr body

and pp_case_branch' e1 f (labels, body) =
  let pp_test f label =
    fprintf f "%a = %a" pp_expr e1 pp_expr label
  in
  fprintf f "%a then %a" (pp_sep_list " \\<or> " pp_test) labels pp_expr body

and show_expr e =
  Format.asprintf "%a" pp_expr e

let pp_func f func_name (ret_type, params, body) =
  fprintf f "definition %s :: \\<open>" func_name;
  List.iter (fun (typ, _) -> fprintf f "%a \\<Rightarrow> " pp_type typ) params;
  fprintf f "%a\\<close> where\n  \\<open>%s" pp_type ret_type func_name;
  List.iter (fun (_, name) -> fprintf f " %s" name) params;
  fprintf f " \\<equiv> %a\\<close>\n" pp_expr body

let pp_record_field struct_name f (typ, field_name) =
  fprintf f "%s_%s :: \\<open>%a\\<close>" struct_name field_name pp_type typ

(* TODO: fix misnomer *)
let pp_reg_assign mod_name f reg_name =
  fprintf f "%s_%s = %s'" mod_name reg_name reg_name

let pp_decl (env : Typing.env) f = function
  | T_Let (name, value) ->
    fprintf f "definition \\<open>%s \\<equiv> %a\\<close>\n"
      name pp_expr value
  | T_FuncDecl { name; ret_type; params; body } ->
    let params' = List.map (fun (typ, name) -> the typ, name) params in
    pp_func f name (the ret_type, params', body)
  | T_ModuleDecl mod_info ->
    let mod_name = mod_info.module_name in
    let state_type_name = mod_name ^ "_state" in

    (* state type *)
    fprintf f "record %s =\n  %a\n" state_type_name
      (pp_sep_list "\n  " (pp_record_field mod_name)) mod_info.regs;
    mod_info.insts |> List.iter begin fun (inst_mod_info, inst_name) ->
      fprintf f "  %s_%s :: \\<open>%s\\<close>\n"
        mod_name inst_name (inst_mod_info.module_name ^ "_state")
    end;

    fprintf f "definition %s_out :: \\<open>" mod_name;
    mod_info.inputs_used_by_out |> List.iter begin fun (typ, name) ->
      fprintf f "%a \\<Rightarrow> " pp_type typ
    end;
    fprintf f "%s \\<Rightarrow> %a\\<close> where\n  \\<open>%s_out"
      state_type_name pp_tuple_type (List.map fst mod_info.outputs) mod_name;
    mod_info.inputs_used_by_out |> List.iter (fun (typ, name) -> fprintf f " %s" name);
    pp_print_string f " \\<S> \\<equiv> ";

    let module G = Graph.Imperative.Digraph.Concrete(String_Key) in
    let module Topo = Graph.Topological.Make(G) in

    (* populate definition table *)
    let def_table = H.create 0 in
    mod_info.items |> List.iter begin function
      | T_AssignItem (name, value) ->
        H.add def_table name (show_expr value)
      | T_RegAssignItem (reg_name, value, guard) ->
        (* current value *)
        H.add def_table reg_name (Printf.sprintf "%s_%s \\<S>" mod_name reg_name);
        let def_text =
          match guard with
          | None -> show_expr value
          | Some g ->
            Printf.sprintf "if %s then %s else %s"
              (show_expr g) (show_expr value) reg_name
        in
        (* next value *)
        H.add def_table (reg_name^"'") def_text
      | T_InstItem inst ->
        let inst_mod_info = inst.mod_info in
        (* string -> int *)
        let defined_name_map =
          let output_index_map, _ =
            List.fold_left (fun (m, i) (_, name) -> M.add name i m, i+1)
              (M.empty, 0) inst_mod_info.outputs
          in
          M.fold begin fun port_name defined_name_opt m ->
            match defined_name_opt with
            | None -> m
            | Some defined_name ->
              let output_index = M.find port_name output_index_map in
              M.add defined_name output_index m
          end inst.output_map M.empty
        and n_output =
          List.length inst_mod_info.outputs
        in
        let tuple_def_text =
          let f = Format.str_formatter in
          fprintf f "%s_out" inst_mod_info.module_name;
          List.iter (fprintf f " %a" pp_expr) inst.used_inputs_out;
          fprintf f " %s" inst.name;
          Format.flush_str_formatter ()
        in
        let rec select acc i n =
          if i > 0 && n > 1 then
            select (Printf.sprintf "snd (%s)" acc) (i-1) (n-1)
          else if n > 1 then
            Printf.sprintf "fst (%s)" acc
          else acc
        in
        (* instance outputs *)
        M.iter begin fun defined_name index ->
          H.add def_table defined_name (select tuple_def_text index n_output)
        end defined_name_map;
        let def_text =
          let f = Format.str_formatter in
          fprintf f "%s_upd" inst_mod_info.module_name;
          List.iter (fprintf f " %a" pp_expr) inst.used_inputs_upd;
          fprintf f " %s" inst.name;
          Format.flush_str_formatter ()
        in
        (* instance state *)
        H.add def_table inst.name (Printf.sprintf "%s_%s \\<S>" mod_name inst.name);
        H.add def_table (inst.name^"'") def_text
    end;

    Topo.iter begin fun name ->
      if S.mem name mod_info.used_names_out then begin
        (*Printf.eprintf "%s\n" name;*)
        match H.find_opt def_table name with
        | None -> () (* input or symbolic constant *)
        | Some def -> fprintf f "let %s = %s in " name def
      end
    end mod_info.val_dep_graph;
    fprintf f "(%a)"
      (pp_comma_sep_list pp_print_string) (List.map snd mod_info.outputs);
    pp_print_string f "\\<close>\n";
    (* the update function *)
    fprintf f "definition %s_upd :: \\<open>" mod_name;
    mod_info.inputs_used_by_upd |> List.iter begin fun (typ, name) ->
      fprintf f "%a \\<Rightarrow> " pp_type typ
    end;
    fprintf f "%s \\<Rightarrow> %s\\<close> where\n  \\<open>%s_upd"
      state_type_name state_type_name mod_name;
    mod_info.inputs_used_by_upd |> List.iter (fun (typ, name) -> fprintf f " %s" name);
    pp_print_string f " \\<S> \\<equiv> ";
    Topo.iter begin fun name ->
      if S.mem name mod_info.used_names_upd then begin
        match H.find_opt def_table name with
        | None -> ()
        | Some def -> fprintf f "let %s = %s in " name def
      end
    end mod_info.val_dep_graph;
    fprintf f "\\<lparr> %a \\<rparr>"
      (pp_comma_sep_list (pp_reg_assign mod_name)) (List.map snd mod_info.regs @ List.map snd mod_info.insts);
    pp_print_string f "\\<close>\n"
  | T_EnumDecl (name, variants) ->
    fprintf f "datatype %s = %a\n"
      name (pp_sep_list " | " pp_print_string) variants
  | T_StructDecl (name, fields) ->
    fprintf f "record %s =\n  %a\n"
      name (pp_sep_list "\n  " (pp_record_field name)) fields

let output_theory module_name env decls =
  let thy_path = module_name ^ "_Spec.thy" in
  let oc = open_out thy_path in
  let f = formatter_of_out_channel oc in
  fprintf f "theory %s_Spec imports \"~~/src/HOL/Word/Word\" begin\n" module_name;
  List.iter (pp_decl env f) decls;
  pp_print_string f "end\n";
  close_out oc
