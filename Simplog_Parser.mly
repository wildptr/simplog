%{
module Syn = Simplog_AST
open Syn
%}

%token EOF
%token <string> Ident

%token <int> Int
%token <Z.t> DecLit
%token <Z.t> BinLit
%token <Z.t> OctLit
%token <Z.t> HexLit

%token <string> String

%token AND
%token ASSIGN
%token BITS
%token BOOL
%token CASE
%token DEFAULT
%token END
%token ENUM
%token FALSE
%token FUNCTION
%token IMPORT
%token IN
%token INPUT
%token INSTANCE
%token LET
%token MODULE
%token OUTPUT
%token PACK
%token REG
%token SIGN_EXTEND
%token SIGNED
%token STRUCT
%token TRUE
%token TYPEDEF
%token UNDEF
%token UNPACK
%token VAL
%token WHEN
%token ZERO_EXTEND

%token And
%token Or
%token Equal
%token NotEqual
%token LE
%token GE
%token SHL
%token SHR
%token ASHR
%token Arrow
%token MapsTo

%token Bang
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
%token LT
%token Eq
%token GT
%token Quest
%token LBrack
%token RBrack
%token Caret
%token LBrace
%token Bar
%token RBrace
%token Tilde

%left Or
%left And
%left Equal NotEqual
%left Bar
%left Caret
%left Amp
%left SIGNED LT GE GT LE
%left SHL SHR ASHR
%left Plus Minus

%start <Simplog_AST.import list * Simplog_AST.decl list> top

%%

top:
  | list(import) list(decl) EOF { $1, $2 }

decl:
  | typedef     { $1 }
  | let_decl    { $1 }
  | func_decl   { $1 }
  | module_decl { $1 }
  | enum_decl   { $1 }
  | struct_decl { $1 }

enum_decl:
  ENUM; name = Ident; LBrace; l = separated_nonempty_list(Comma, Ident); RBrace; Semi
    { EnumDecl (name, l) }

struct_decl:
  STRUCT; name = Ident; LBrace; l = list(struct_field); RBrace; Semi
    { StructDecl (name, l) }

import:
  IMPORT option(String) separated_nonempty_list(Comma, Ident) Semi { $2, $3 }

typedef: TYPEDEF type_ Ident Semi { Typedef ($2, $3) }

type_:
(*| Ident; loption(delimited(LParen, separated_nonempty_list(Comma, type_), RParen))
    { TypeIdent ($1, $2) }*)
  | Ident
    { TypeIdent ($1, $loc) }
  | BITS; LParen; width = Int; RParen
    { BitsType width }
(*| ENUM; LBrace; l = separated_nonempty_list(Comma, Ident); RBrace
    { EnumType l }
  | STRUCT; LBrace; l = list(struct_field); RBrace
    { StructType l }*)
  | LParen type_ RParen { $2 }
  | LParen; hd = type_; Comma; tl = separated_nonempty_list(Comma, type_); RParen
    { TupleType (hd::tl) }
  | BOOL { BoolType }
  | t1 = type_; LBrack; t2 = type_; RBrack { MapType (t1, t2) }

struct_field: type_ Ident Semi { $1, $2 }

let_decl:
  LET; name = Ident; Eq; value = expr; Semi
    { Let (name, value) }

let_expr_rest:
  AND; name = Ident; Eq; value = expr
    { name, value }

literal:
(*| DecLit      { LitExpr (None, Dec, $1) }
  | BinLit      { LitExpr (None, Bin, $1) }
  | OctLit      { LitExpr (None, Oct, $1) }
  | HexLit      { LitExpr (None, Hex, $1) }*)
  | Int DecLit  { LitExpr ($1, Dec, $2) }
  | Int BinLit  { LitExpr ($1, Bin, $2) }
  | Int OctLit  { LitExpr ($1, Oct, $2) }
  | Int HexLit  { LitExpr ($1, Hex, $2) }

expr: let_expr { $1 }

atom_expr:
(*| Int         {{ e_loc = $loc; e_kind = IntExpr $1 }}*)
  | Ident       {{ e_loc = $loc; e_type = None; e_kind = IdentExpr $1 }}
  | TRUE        {{ e_loc = $loc; e_type = None; e_kind = BoolExpr true }}
  | FALSE       {{ e_loc = $loc; e_type = None; e_kind = BoolExpr false }}
  | literal     {{ e_loc = $loc; e_type = None; e_kind = $1 }}
  | LParen expr RParen
                {{ $2 with e_loc = $loc }}
  | LParen; hd = expr; Comma; tl = separated_nonempty_list(Comma, expr); RParen
                {{ e_loc = $loc; e_type = None; e_kind = TupleExpr (hd::tl) }}
  | struct_literal
                {{ e_loc = $loc; e_type = None; e_kind = $1 }}
  | UNDEF LParen type_ RParen
                {{ e_loc = $loc; e_type = None; e_kind = UndefExpr $3 }}
  | case_e      {{ e_loc = $loc; e_type = None; e_kind = $1 }}
  | concat_e    {{ e_loc = $loc; e_type = None; e_kind = $1 }}
  | replicate_e {{ e_loc = $loc; e_type = None; e_kind = $1 }}
  | func_name=Ident LParen args=separated_nonempty_list(Comma, expr) RParen
                {{ e_loc = $loc; e_type = None; e_kind = ApplyExpr (func_name, args) }}
(*| PACK LParen e=expr RParen
                {{ e_loc = $loc; e_type = None; e_kind = PackExpr e }}*)
  | ZERO_EXTEND LParen len=Int Comma e=expr RParen
                {{ e_loc = $loc; e_type = None; e_kind = ExtendExpr (false, len, e) }}
  | SIGN_EXTEND LParen len=Int Comma e=expr RParen
                {{ e_loc = $loc; e_type = None; e_kind = ExtendExpr (true, len, e) }}

replicate_e:
  LBrace n=Int LBrace e=expr RBrace RBrace { ReplicateExpr (n, e) }

concat_e:
  LBrace separated_nonempty_list(Comma, expr) RBrace { ConcatExpr $2 }

case_e:
  CASE; LParen; e = expr; RParen; branches = list(case_branch); END
    { CaseExpr (e, branches) }

case_branch: case_label Colon expr Semi { $1, $3 }

case_label:
  | separated_nonempty_list(Comma, expr) { Some $1 }
  | DEFAULT { None }

prefix_expr:
  | postfix_expr { $1 }
  | Bang  prefix_expr   {{ e_loc = $loc; e_type = None; e_kind = UnExpr(Not,    $2) }}
  | Tilde prefix_expr   {{ e_loc = $loc; e_type = None; e_kind = UnExpr(LogNot, $2) }}

bin_expr:
  | prefix_expr { $1 }
  | bin_expr Plus     bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Add,    $1, $3) }}
  | bin_expr Minus    bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Sub,    $1, $3) }}
  | bin_expr Amp      bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (LogAnd, $1, $3) }}
  | bin_expr Caret    bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (LogXor, $1, $3) }}
  | bin_expr Bar      bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (LogOr,  $1, $3) }}
  | bin_expr And      bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Syn.And,  $1, $3) }}
  | bin_expr Or       bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Syn.Or,   $1, $3) }}
  | bin_expr SHL      bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Syn.SHL,  $1, $3) }}
  | bin_expr SHR      bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Syn.LSHR, $1, $3) }}
  | bin_expr ASHR     bin_expr  {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Syn.ASHR, $1, $3) }}

  | bin_expr Equal       bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (Syn.Eq,   $1, $3) }}
  | bin_expr NotEqual    bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (NotEq,  $1, $3) }}
  | bin_expr SIGNED   LT bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (SLT,    $1, $4) }}
  | bin_expr          LT bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (ULT,    $1, $3) }}
  | bin_expr SIGNED   GE bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (SGE,    $1, $4) }}
  | bin_expr          GE bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (UGE,    $1, $3) }}
  | bin_expr SIGNED   GT bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (SGT,    $1, $4) }}
  | bin_expr          GT bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (UGT,    $1, $3) }}
  | bin_expr SIGNED   LE bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (SLE,    $1, $4) }}
  | bin_expr          LE bin_expr       {{ e_loc = $loc; e_type = None; e_kind = BinExpr (ULE,    $1, $3) }}

postfix_expr:
  | atom_expr { $1 }
  | e=postfix_expr LBrack hi=Int Colon lo=Int RBrack
    {{ e_loc = $loc; e_type = None; e_kind = RangeSelectExpr (e, hi, lo, ($startpos(hi), $endpos(lo))) }}
  | e=postfix_expr LBrack i=Int RBrack
    {{ e_loc = $loc; e_type = None; e_kind = BitSelectExpr (e, i, $loc(i)) }}
  | e=postfix_expr Dot name=Ident
    {{ e_loc = $loc; e_type = None; e_kind = FieldSelectExpr (e, name, $loc(name)) }}
  | e1=postfix_expr LBrack e2=expr RBrack
    {{ e_loc = $loc; e_type = None; e_kind = IndexExpr (e1, e2) }}
  | e1=postfix_expr LBrack e2=expr MapsTo e3=expr RBrack
    {{ e_loc = $loc; e_type = None; e_kind = UpdateExpr (e1, e2, e3) }}

let_expr:
  | cond_expr { $1 }
  | LET; name = Ident; Eq; value = expr; rest = list(let_expr_rest); IN; body = expr
    {{ e_loc = $loc; e_type = None; e_kind = LetExpr ((name, value) :: rest, body) }}

cond_expr:
  | bin_expr { $1 }
  | e1=bin_expr Quest e2=expr Colon e3=cond_expr
    {{ e_loc = $loc; e_type = None; e_kind = CondExpr (e1, e2, e3) }}

field:
  | Ident               { $1, $loc($1), { e_loc = $loc; e_type = None; e_kind = IdentExpr $1 } }
  | Ident Colon expr    { $1, $loc($1), $3 }

struct_literal:
  type_name = Ident; LBrace; l = separated_nonempty_list(Comma, field); RBrace
    { StructExpr (type_name, $loc(type_name), l) }

param: type_ Ident { $1, $2 }

func_decl:
  FUNCTION; ret_type = type_; name = Ident; params = delimited(LParen, separated_nonempty_list(Comma, param), RParen); Eq; body = expr; Semi
    { FuncDecl { name; ret_type; params; body } }

port_direction:
  | INPUT       { Input }
  | OUTPUT      { Output }

port:
  port_direction type_ Ident { $1, $2, $3 }

module_decl:
  MODULE; name = Ident; ports = loption(delimited(LParen, separated_nonempty_list(Comma, port), RParen));
  decls = list(module_comp_decl); items = list(module_item); END; Semi
    { ModuleDecl { name; ports; decls; items } }

module_comp_decl:
  | val_decl    { $1 }
  | reg_decl    { $1 }
  | inst_decl   { $1 }

module_item:
  | inst_mod_item       { $1 }
  | assign_mod_item     { $1 }
  | reg_assign_mod_item { $1 }

val_decl:
  VAL type_ separated_nonempty_list(Comma, Ident) Semi
    { ValDecl ($2, $3) }

reg_decl:
  REG type_ separated_nonempty_list(Comma, Ident) Semi
    { RegDecl ($2, $3) }

inst_decl:
  INSTANCE mod_name = Ident; inst_names = separated_nonempty_list(Comma, Ident); Semi
    { InstDecl (mod_name, inst_names) }

inst_mod_item:
  inst_name = Ident; LParen; ports = separated_nonempty_list(Comma, field); RParen; Semi
    { InstItem (inst_name, ports, $loc) }

assign_mod_item:
  Ident Eq expr Semi { AssignItem ($1, $loc($1), $3) }

reg_assign_mod_item:
  name = Ident; LE; value = expr; guard = option(preceded(WHEN, expr)); Semi
    { RegAssignItem (name, $loc(name), value, guard) }
