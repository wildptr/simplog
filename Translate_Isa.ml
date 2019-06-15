open Simplog_AST
open ExtLib

open Format

module P = Simplog_Program

let pp_sep_list sep pp f = function
  | [] -> ()
  | hd::tl ->
    pp f hd;
    List.iter (fprintf f "%s%a" sep pp) tl

let pp_comma_sep_list pp f = pp_sep_list ", " pp f

let rec pp_type f = function
  | P.BoolType -> pp_print_string f "bool"
  | P.BitsType len -> fprintf f "%d word" len
  | P.EnumType (name, _) | P.StructType (name, _) ->
    pp_print_string f name
  | P.TupleType types -> pp_sep_list " \\<times> " pp_type f types

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
    let [@warning "-8"] Some (P.StructType (_, fields_def)) = e.e_type in
    (pp_comma_sep_list pp_field f) (reorder_fields fields fields_def);
    pp_print_string f " \\<rparr>"
  | ApplyExpr (func_name, args) ->
    pp_print_char f '(';
    pp_print_string f func_name;
    List.iter (fprintf f " %a" pp_expr) args;
    pp_print_char f ')'
  | CaseExpr (e1, branches) ->
    let expanded_branches =
      List.map (fun (labels, body) -> List.map (fun label -> label, body) labels) branches |> List.concat
    in
    begin match Option.get e1.e_type with
      | P.BoolType | P.EnumType _ ->
        fprintf f "(case %a of %a)" pp_expr e1 (pp_sep_list " | " pp_case_branch) expanded_branches
      | P.BitsType _ ->
        (* "if %a = %a then %a else if %a = %a then %a else undefined" *)
        fprintf f "(if %a else undefined)" (pp_sep_list " else if " (pp_case_branch' e1)) expanded_branches
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
    pp_print_string f "undefined"
  | RangeSelectExpr (e1, hi, lo, _) ->
    begin match e1.e_type with
      | None ->
        let pos = fst e1.e_loc in
        Printf.eprintf "%s:%d:%d: expr has no type!?\n"
          pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
        assert false
      | Some (P.BitsType len) -> ()
      | Some _ -> assert false
    end;
    let [@warning "-8"] Some (P.BitsType len) = e1.e_type in
    fprintf f "((ucast (slice %d %a :: %d word)) :: %d word)"
      lo pp_expr e1 (len-lo) (hi+1-lo)
  | BitSelectExpr (e1, i, _) ->
    fprintf f "(%a !! %d)" pp_expr e1 i
  | FieldSelectExpr (e1, field_name, _) ->
    fprintf f "(%s' %a)" field_name pp_expr e1
  | TupleExpr es ->
    fprintf f "(%a)" (pp_comma_sep_list pp_expr) es

and pp_field f (name, _, value) =
  fprintf f "%s' = %a" name pp_expr value

and pp_case_branch f (label, body) =
  fprintf f "%a \\<Rightarrow> %a" pp_expr label pp_expr body

and pp_case_branch' e1 f (label, body) =
  fprintf f "%a = %a then %a" pp_expr e1 pp_expr label pp_expr body

let pp_func f func_name (ret_type, params, body) =
  fprintf f "definition %s :: \\<open>" func_name;
  List.iter (fun (typ, _) -> fprintf f "%a \\<Rightarrow> " pp_type typ) params;
  fprintf f "%a\\<close>\n  where \\<open>%s" pp_type ret_type func_name;
  List.iter (fun (_, name) -> fprintf f " %s" name) params;
  fprintf f " \\<equiv> %a\\<close>\n" pp_expr body

let pp_record_field f (typ, name) =
  fprintf f "%s' :: \\<open>%a\\<close>" name pp_type typ

let pp_decl f = function
  | T_Let (name, value) ->
    fprintf f "definition \\<open>%s \\<equiv> %a\\<close>\n"
      name pp_expr value
  | T_FuncDecl { name; ret_type; params; body } ->
    pp_func f name (ret_type, params, body)
  | T_ModuleDecl _ -> () (* TODO *)
  | T_EnumDecl (name, variants) ->
    fprintf f "datatype %s = %a\n"
      name (pp_sep_list " | " pp_print_string) variants
  | T_StructDecl (name, fields) ->
    fprintf f "record %s =\n  %a\n"
      name (pp_sep_list "\n  " pp_record_field) fields

let output_theory module_name decls =
  let thy_path = module_name ^ "_Spec.thy" in
  let oc = open_out thy_path in
  let f = formatter_of_out_channel oc in
  fprintf f "theory %s_Spec imports Main \"~~/src/HOL/Word/Word\" begin\n" module_name;
  List.iter (pp_decl f) decls;
  pp_print_string f "end\n";
  close_out oc
