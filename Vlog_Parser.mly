%{
module S = Vlog_AST
open S
%}

%token EOF
%token <Z.t> DecLit
%token <Z.t> BinLit
%token <Z.t> OctLit
%token <Z.t> HexLit
%token <string> Ident
%token <int> Int

%token BangEq
%token PlusColon
%token LtLt
%token LtEq
%token EqEq
%token GtEq
%token GtGt

%token Bang
%token Hash
%token Amp
%token LParen
%token RParen
%token Star
%token Plus
%token Comma
%token Minus
%token Dot
%token Colon
%token Semi
%token Lt
%token Eq
%token Gt
%token Quest
%token At
%token LBrack
%token RBrack
%token Caret
%token LBrace
%token Bar
%token RBrace
%token Tilde

%token ALWAYS
%token ASSIGN
%token BEGIN
%token CASE
%token CASEX
%token CASEZ
%token DEFAULT
%token ELSE
%token END
%token ENDCASE
%token ENDMODULE
%token IF
%token INOUT
%token INPUT
%token LOCALPARAM
%token MODULE
%token NEGEDGE
%token OUTPUT
%token PARAMETER
%token POSEDGE
%token REG
%token WIRE

%start <Vlog_AST.module_> top
%type <signal_type> signal_type
%type <signal_decl> signal_decl
%type <instance> instance
%type <always_block> always_block
%type <assign> assign
%type <port_decl> port_decl
%type <item> item
%type <expr> expr
%type <proc> proc

(* for resolving if-else conflict *)
%nonassoc RParen
%nonassoc ELSE

(* for resolving port declaration conflict *)

%%

top:
  | module_ EOF {$1}

module_:
  | MODULE; name = Ident;
    params = loption(preceded(Hash, delimited(LParen, comma_sep_signal_decl_list, RParen)));
    ports = delimited(LParen, comma_sep_port_decl_list, RParen); Semi;
    items = list(item); ENDMODULE
    { make_module_new name params ports items }
  | MODULE; name = Ident;
    params = loption(preceded(Hash, delimited(LParen, comma_sep_signal_decl_list, RParen)));
    ports = loption(delimited(LParen, separated_list(Comma, Ident), RParen)); Semi;
    items = list(item); ENDMODULE
    { make_module_old name params ports items }

(* prevents an unresolvable shift/reduce conflict on Comma *)
comma_sep_signal_decl_list:
  | signal_decl {[$1]}
  | signal_decl_comma comma_sep_signal_decl_list {$1::$2}

port_direction:
  | INPUT  { Input  }
  | OUTPUT { Output }
  | INOUT  { Inout  }

range_spec:
  | LBrack; msb = expr; Colon; lsb = expr; RBrack
    { msb, lsb }

comma_sep_port_decl_list:
  | port_decl {[$1]}
  | port_decl_comma comma_sep_port_decl_list {$1::$2}

port_decl:
  | port_dir = port_direction; port_is_reg = boption(REG);
    port_range_opt = range_spec?;
    port_declarators = separated_nonempty_list(Comma, signal_declarator)
    {{ port_dir; port_is_reg; port_range_opt; port_declarators }}

port_decl_comma:
  | port_dir = port_direction; port_is_reg = boption(REG);
    port_range_opt = range_spec?;
    port_declarators = list(terminated(signal_declarator, Comma))
    {{ port_dir; port_is_reg; port_range_opt; port_declarators }}

assign_lhs:
  | name = Ident; indices = list(index)
    {{ e_desc = E_select (name, indices); e_loc = $loc }}
  | LBrace; exprs = separated_nonempty_list(Comma, assign_lhs); RBrace
    {{ e_desc = E_concat exprs; e_loc = $loc }}

index:
  | LBrack; msb = expr; Colon; lsb = expr; RBrack
    { Part_const (msb, lsb) }
  | LBrack; bit = expr; RBrack
    { Bit bit }
  | LBrack; base = expr; PlusColon; width = expr; RBrack
    { Part_var (base, width) }

primary_expr:
  | Int
    {{ e_desc = E_int $1; e_loc = $loc }}
  | Int DecLit {{ e_desc = E_bitvec (Dec, Some $1, $2); e_loc = $loc }}
  | Int BinLit {{ e_desc = E_bitvec (Bin, Some $1, $2); e_loc = $loc }}
  | Int OctLit {{ e_desc = E_bitvec (Oct, Some $1, $2); e_loc = $loc }}
  | Int HexLit {{ e_desc = E_bitvec (Hex, Some $1, $2); e_loc = $loc }}
  | DecLit {{ e_desc = E_bitvec (Dec, None, $1); e_loc = $loc }}
  | BinLit {{ e_desc = E_bitvec (Bin, None, $1); e_loc = $loc }}
  | OctLit {{ e_desc = E_bitvec (Oct, None, $1); e_loc = $loc }}
  | HexLit {{ e_desc = E_bitvec (Hex, None, $1); e_loc = $loc }}
  | name = Ident; indices = list(index)
    {{ e_desc = E_select (name, indices); e_loc = $loc }}
  | LParen; e = expr; RParen {{ e with e_loc = $loc }}
  | LBrace; exprs = separated_nonempty_list(Comma, expr); RBrace
    {{ e_desc = E_concat exprs; e_loc = $loc }}
  | LBrace; n = expr; LBrace; e = expr; RBrace; RBrace
    {{ e_desc = E_duplicate (n, e); e_loc = $loc }}

prefix_op:
  | Tilde { Not        }
  | Amp   { Reduce_And }
  | Bar   { Reduce_Or  }

prefix_expr:
  | primary_expr {$1}
  | op = prefix_op; e = prefix_expr
    {{ e_desc = E_unary (op, e); e_loc = $loc }}

mul_op:
  | Star { Mul }

mul_expr:
  | e = prefix_expr {e}
  | e1 = mul_expr; op = mul_op; e2 = prefix_expr
    {{ e_desc = E_binary (op, e1, e2); e_loc = $loc }}

add_op:
  | Plus  { Add }
  | Minus { Sub }

add_expr:
  | e = mul_expr {e}
  | e1 = add_expr; op = add_op; e2 = mul_expr
    {{ e_desc = E_binary (op, e1, e2); e_loc = $loc }}

shift_op:
  | LtLt { ShiftL }
  | GtGt { ShiftR }

shift_expr:
  | e = add_expr {e}
  | e1 = shift_expr; op = shift_op; e2 = add_expr
    {{ e_desc = E_binary (op, e1, e2); e_loc = $loc }}

rel_op:
  | Lt   { S.Lt }
  | GtEq { S.GtEq }
  | Gt   { S.Gt }
  | LtEq { S.LtEq }

rel_expr:
  | e = shift_expr {e}
  | e1 = rel_expr; op = rel_op; e2 = shift_expr
    {{ e_desc = E_binary (op, e1, e2); e_loc = $loc }}

eq_op:
  | EqEq   { S.Eq  }
  | BangEq { NotEq }

eq_expr:
  | e = rel_expr {e}
  | e1 = eq_expr; op = eq_op; e2 = rel_expr
    {{ e_desc = E_binary (op, e1, e2); e_loc = $loc }}

and_expr:
  | e = eq_expr {e}
  | e1 = and_expr; Amp; e2 = eq_expr
    {{ e_desc = E_binary (And, e1, e2); e_loc = $loc }}

xor_expr:
  | e = and_expr {e}
  | e1 = xor_expr; Caret; e2 = and_expr
    {{ e_desc = E_binary (Xor, e1, e2); e_loc = $loc }}

or_expr:
  | e = xor_expr {e}
  | e1 = xor_expr; Bar; e2 = or_expr
    {{ e_desc = E_binary (Or, e1, e2); e_loc = $loc }}

cond_expr:
  | e = or_expr {e}
  | e_cond = or_expr; Quest; e_true = expr; Colon; e_false = expr
    {{ e_desc = E_cond (e_cond, e_true, e_false); e_loc = $loc }}

expr:
  | e = cond_expr {e}

assign:
  | ASSIGN; lhs = assign_lhs; Eq; rhs = expr; Semi
    { lhs, rhs }

signal_type:
  | WIRE { Wire }
  | REG  { Reg  }
  | LOCALPARAM { Localparam }
  | PARAMETER  { Parameter  }

signal_declarator:
  | name = Ident; array_dim = list(range_spec);
    eq_expr_opt = preceded(Eq, expr)?
    {{ sig_name = name; sig_dims = array_dim; sig_value_opt = eq_expr_opt }}

signal_decl:
  | sig_type = signal_type; sig_range_opt = range_spec?;
    sig_declarators = separated_nonempty_list(Comma, signal_declarator);
    {{ sig_type; sig_range_opt; sig_declarators }}

signal_decl_comma:
  | sig_type = signal_type; sig_range_opt = range_spec?;
    sig_declarators = list(terminated(signal_declarator, Comma));
    {{ sig_type; sig_range_opt; sig_declarators }}

inst_connection:
  | Dot; port_name = Ident; LParen; port_expr_opt = expr?; RParen
    { port_name, port_expr_opt }

instance:
  | inst_class_name = Ident; inst_inst_name = Ident; LParen;
    inst_connections = separated_nonempty_list(Comma, inst_connection);
    RParen; Semi
    {{ inst_class_name; inst_inst_name; inst_connections }}

case_keyword:
  | CASE  { Case  }
  | CASEX { Casex }
  | CASEZ { Casez }

case_expr:
  | DEFAULT { None }
  | e = expr { Some e }

case_branch:
  | expr_opt = case_expr; Colon; proc = proc { expr_opt, proc }

proc:
  | lhs = assign_lhs; Eq; rhs = expr; Semi
    { P_blocking_assign (lhs, rhs) }
  | lhs = assign_lhs; LtEq; rhs = expr; Semi
    { P_nonblocking_assign (lhs, rhs) }
  | BEGIN; procs = list(proc); END
    { P_comp procs }
  | IF; LParen; cond = expr; RParen; proc_t = proc
    { P_if (cond, proc_t, None) }
  | IF; LParen; cond = expr; RParen; proc_t = proc; ELSE; proc_f = proc
    { P_if (cond, proc_t, Some proc_f) }
  | variant = case_keyword; LParen; switch_expr = expr; RParen;
    branches = list(case_branch); ENDCASE
    { P_case (variant, switch_expr, branches) }

sensitivity:
  | Star { Sens_auto }
  | POSEDGE; name = Ident { Sens_posedge name }
  | NEGEDGE; name = Ident { Sens_negedge name }
  | LParen; s = sensitivity; RParen {s}

always_block:
  | ALWAYS; At; sens = sensitivity; proc = proc
    { sens, proc }

item:
  | signal_decl Semi
    { Item_signal $1 }
  | assign
    { Item_assign $1 }
  | instance
    { Item_instance $1 }
  | always_block
    { Item_always $1 }
  | port_decl Semi
    { Item_port_decl $1 }

(* vim: set indentexpr=: *)
