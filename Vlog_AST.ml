open ExtLib

type signal_type =
  | Wire
  | Reg
  | Localparam
  | Parameter

let pp_signal_type f sig_ =
  let open Format in
  match sig_ with
  | Wire -> fprintf f "wire"
  | Reg -> fprintf f "reg"
  | Localparam -> fprintf f "localparam"
  | Parameter -> fprintf f "parameter"

type sensitivity =
  | Sens_auto
  | Sens_posedge of string
  | Sens_negedge of string

let pp_sensitivity f sens =
  let open Format in
  match sens with
  | Sens_auto -> fprintf f "*"
  | Sens_posedge s -> fprintf f "(posedge %s)" s
  | Sens_negedge s -> fprintf f "(negedge %s)" s

type case_variant =
  | Case
  | Casex
  | Casez

let pp_case_variant f case =
  let open Format in
  match case with
  | Case -> fprintf f "case"
  | Casex -> fprintf f "casex"
  | Casez -> fprintf f "casez"

(* Binary operators are listed in precedence order, from high to low.
 * Operators with same precedence are listed on the same line. *)
type binary_op =
  | Mul
  | Add | Sub
  | ShiftL | ShiftR
  | Lt | GtEq | Gt | LtEq
  | Eq | NotEq
  | And
  | Or
  | Xor

(* let prec_of_binary_op = function
  | B_mul -> 0
  | B_add | B_sub -> 1
  | B_shiftL | B_shiftR -> 2
  | B_lt | B_ge | B_gt | B_le -> 3
  | B_eq | B_neq -> 4
  | B_and -> 5
  | B_or -> 6
  | B_xor -> 7 *)

let string_of_binary_op = function
  | Mul -> "*"
  | Add -> "+"
  | Sub -> "-"
  | ShiftL -> "<<"
  | ShiftR -> ">>"
  | Lt -> "<"
  | GtEq -> ">="
  | Gt -> ">"
  | LtEq -> "<="
  | Eq -> "=="
  | NotEq -> "!="
  | And -> "&"
  | Or -> "|"
  | Xor -> "^"

type unary_op =
  | Not
  | Reduce_And
  | Reduce_Or

let string_of_unary_op = function
  | Not -> "~"
  | Reduce_And -> "&"
  | Reduce_Or -> "|"

type radix = Dec | Bin | Oct | Hex

type expr_desc =
  | E_select of string * index list
  | E_int of int
  | E_bitvec of radix * int option * Z.t
  | E_cond of expr * expr * expr
  | E_binary of binary_op * expr * expr
  | E_unary of unary_op * expr
  | E_concat of expr list
  | E_duplicate of expr * expr

and expr = {
  e_desc : expr_desc;
  e_loc : Lexing.position * Lexing.position
}

and index =
  | Bit of expr
  | Part_const of expr * expr
  | Part_var of expr * expr

let rec pp_expr f expr =
  let open Format in
  match expr.e_desc with
  | E_select (name, indices) ->
      fprintf f "%s" name;
      List.iter (pp_index f) indices
  | E_int n ->
    pp_print_int f n
  | E_bitvec (radix, width_opt, value) ->
    let width_str =
      match width_opt with
      | Some width -> string_of_int width
      | None -> ""
    and radix_char =
      match radix with 
      | Dec -> 'd'
      | Bin -> 'b'
      | Oct -> 'o'
      | Hex -> 'h'
    in
    (* TODO *)
    fprintf f "%s'%c..." width_str radix_char
  | E_cond (e_cond, e_true, e_false) ->
      fprintf f "(%a ? %a : %a)"
        pp_expr e_cond pp_expr e_true pp_expr e_false
  | E_binary (op, e1, e2) ->
      fprintf f "(%a %s %a)"
        pp_expr e1 (string_of_binary_op op) pp_expr e2
  | E_unary (op, e) ->
      fprintf f "(%s%a)" (string_of_unary_op op) pp_expr e
  | E_concat es ->
      fprintf f "{";
      let n = List.length es in
      es |> List.iteri begin fun i e ->
        pp_expr f e;
        if i < n-1 then fprintf f ","
      end;
      fprintf f "}"
  | E_duplicate (e_n, e_data) ->
      fprintf f "{%a{%a}}" pp_expr e_n pp_expr e_data

and pp_index f index =
  let open Format in
  match index with
  | Bit e ->
      fprintf f "[%a]" pp_expr e
  | Part_const (e_msb, e_lsb) ->
      fprintf f "[%a:%a]" pp_expr e_msb pp_expr e_lsb
  | Part_var (e_base, e_width) ->
      fprintf f "[%a+:%a]" pp_expr e_base pp_expr e_width

type assign = expr * expr

type proc =
  | P_blocking_assign of assign
  | P_nonblocking_assign of assign
  | P_comp of proc list
  | P_if of expr * proc * proc option
  | P_case of case_variant * expr * (expr option * proc) list

let rec pp_proc ind f proc =
  let open Format in
  match proc with
  | P_blocking_assign (lhs, rhs) ->
      fprintf f "%s%a = %a;\n" ind pp_expr lhs pp_expr rhs
  | P_nonblocking_assign (lhs, rhs) ->
      fprintf f "%s%a <= %a;\n" ind pp_expr lhs pp_expr rhs
  | P_comp procs ->
      fprintf f "%sbegin\n" ind;
      List.iter (pp_proc (ind^"  ") f) procs;
      fprintf f "%send\n" ind
  | P_if (e_cond, p_true, p_false_opt) ->
    let ind' = ind ^ "  " in
    fprintf f "%sif (%a)\n%a" ind pp_expr e_cond (pp_proc ind') p_true;
      begin match p_false_opt with
      | None -> ()
      | Some p_false ->
          fprintf f "%selse\n%a" ind (pp_proc ind') p_false
      end
  | P_case (variant, e_disc, branches) ->
    let ind' = ind ^ "  " in
    fprintf f "%s%a (%a)\n" ind pp_case_variant variant pp_expr e_disc;
    branches |> List.iter begin fun (label_expr_opt, proc) ->
      begin match label_expr_opt with
        | None -> fprintf f "%sdefault:\n" ind
        | Some label_expr -> fprintf f "%s%a:\n" ind pp_expr label_expr
      end;
      pp_proc ind' f proc
    end;
    fprintf f "%sendcase\n" ind

type signal_declarator = {
  sig_name : string;
  sig_dims : (expr * expr) list;
  sig_value_opt : expr option
}

let pp_signal_declarator f s =
  let open Format in
  fprintf f "%s" s.sig_name;
  s.sig_dims |> List.iter begin fun (e1, e2) ->
    fprintf f "[%a:%a]" pp_expr e1 pp_expr e2
  end;
  match s.sig_value_opt with
  | None -> ()
  | Some value -> fprintf f " = %a" pp_expr value

type signal_decl = {
  sig_type : signal_type;
  sig_range_opt : (expr * expr) option;
  sig_declarators : signal_declarator list;
}

type port_direction = Input | Output | Inout

let string_of_port_direction = function
  | Input -> "input"
  | Output -> "output"
  | Inout -> "inout"

type port_decl = {
  port_dir : port_direction;
  port_is_reg : bool;
  port_range_opt : (expr * expr) option;
  port_declarators : signal_declarator list;
}

let pp_range f (msb, lsb) =
  Format.fprintf f "[%a:%a]" pp_expr msb pp_expr lsb

let pp_port_decl f port =
  let open Format in
  fprintf f "%s%s"
    (string_of_port_direction port.port_dir)
    (if port.port_is_reg then " reg" else "");
  begin match port.port_range_opt with
  | None -> ()
  | Some range -> fprintf f " %a" pp_range range
  end;
  fprintf f " ";
  let n = List.length port.port_declarators in
  port.port_declarators |> List.iteri begin fun i declr ->
    pp_signal_declarator f declr;
    if i < n-1 then fprintf f ", "
  end

let pp_signal_decl f sigdecl =
  let open Format in
  fprintf f "%a" pp_signal_type sigdecl.sig_type;
  begin match sigdecl.sig_range_opt with
  | None -> ()
  | Some range -> fprintf f " %a" pp_range range
  end;
  fprintf f " ";
  let n = List.length sigdecl.sig_declarators in
  sigdecl.sig_declarators |> List.iteri begin fun i declr ->
    pp_signal_declarator f declr;
    if i < n-1 then fprintf f ", "
  end

type instance = {
  inst_class_name : string;
  inst_inst_name : string;
  inst_connections : (string * expr option) list;
}

let pp_instance f inst =
  let open Format in
  fprintf f "%s %s(" inst.inst_class_name inst.inst_inst_name;
  let n = List.length inst.inst_connections in
  inst.inst_connections |> List.iteri begin fun i (name, expr_opt) ->
    pp_print_string f "\n  ";
    begin match expr_opt with
      | None -> fprintf f ".%s()" name
      | Some expr -> fprintf f ".%s(%a)" name pp_expr expr
    end;
    if i < n-1 then fprintf f ","
  end;
  fprintf f "\n);\n"

type always_block = sensitivity * proc

let pp_always_block f (sens, proc) =
  Format.fprintf f "always @@%a\n%a" pp_sensitivity sens (pp_proc "  ") proc

type item =
  | Item_signal of signal_decl
  | Item_assign of assign
  | Item_instance of instance
  | Item_always of always_block
  | Item_port_decl of port_decl

let pp_item f = function
  | Item_signal sigdecl -> Format.fprintf f "%a;\n" pp_signal_decl sigdecl
  | Item_assign (lhs, rhs) ->
    Format.fprintf f "assign %a = %a;\n" pp_expr lhs pp_expr rhs
  | Item_instance inst -> pp_instance f inst
  | Item_always always -> pp_always_block f always
  | Item_port_decl port_decl ->
    Format.fprintf f "%a;\n" pp_port_decl port_decl

type module_ = {
  mod_name : string;
  mod_params : signal_decl list;
  mod_ports : string list;
  mod_items : item list;
}

let pp_module f m =
  let open Format in
  fprintf f "module %s" m.mod_name;
(*if m.mod_params <> [] then begin
    fprintf f "#(";
    let n = List.length m.mod_params in
    m.mod_params |> List.iteri (fun i sigdecl ->
      pp_signal_decl f sigdecl;
      if i < n-1 then fprintf f ", ");
    fprintf f ");";
  end;*)
(*fprintf f "(";
  let n = List.length m.mod_ports in
  m.mod_ports |> List.iteri (fun i port_decl ->
    fprintf f "\n  %a" pp_port_decl port_decl;
    if i < n-1 then fprintf f ",");
  fprintf f "\n);\n";*)
  begin match m.mod_ports with
  | [] -> ()
  | hd::tl ->
    fprintf f "(%s" hd;
    List.iter (fprintf f ", %s") tl;
    pp_print_char f ')';
  end;
  pp_print_char f '\n';
  List.iter (pp_item f) m.mod_items;
  fprintf f "endmodule"

let make_module_old name params ports items =
  { mod_name = name;
    mod_params = params;
    mod_ports = ports;
    mod_items = items }

let make_module_new name params ports items =
  let mod_ports =
    ports |> List.map begin fun port_decl ->
      port_decl.port_declarators |> List.map (fun sig_decl -> sig_decl.sig_name)
    end |> List.concat
  in
  { mod_name = name;
    mod_params = params;
    mod_ports;
    mod_items = items }
