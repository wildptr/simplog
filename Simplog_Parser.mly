%{
module S = Simplog_AST
open S
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
%token CASE
%token END
%token ENUM
%token FALSE
%token FUNCTION
%token IMPORT
%token IN
%token INPUT
%token LET
%token MODULE
%token OUTPUT
%token STRUCT
%token TRUE
%token TYPEDEF
%token UNDEF
%token VAL

%token And
%token Equal
%token NotEqual
%token Or

%token Amp
%token LParen
%token RParen
%token Plus
%token Comma
%token Minus
%token Dot
%token Colon
%token Semi
%token Quest
%token LBrack
%token RBrack
%token Caret
%token LBrace
%token Bar
%token RBrace
%token Eq

%left Or
%left And
%left Bar
%left Caret
%left Amp
%left Equal NotEqual
%left Plus Minus

%start <Simplog_AST.decl list> top
%%

top:
  | list(decl) EOF {$1}

decl:
  | typedef     { $1 }
  | import      { $1 }
  | let_decl    { $1 }
  | func_decl   { $1 }
  | module_decl { $1 }

import:
  IMPORT option(String) separated_nonempty_list(Comma, Ident) Semi
    { Import ($2, $3) }

typedef: TYPEDEF type_ Ident Semi { Typedef ($2, $3) }

type_:
  | Ident; loption(delimited(LParen, separated_nonempty_list(Comma, type_), RParen))
    { TypeIdent ($1, $2) }
  | BITS; LParen; width = Int; RParen
    { BitsType width }
  | ENUM; LBrace; l = separated_nonempty_list(Comma, Ident); RBrace
    { EnumType l }
  | STRUCT; LBrace; l = list(struct_field); RBrace
    { StructType l }

struct_field: type_ Ident Semi { $1, $2 }

let_decl:
  LET; name = Ident; Eq; value = expr; Semi
    { Let (name, value) }

let_expr_rest:
  AND; name = Ident; Eq; value = expr
    { name, value }

literal:
  | DecLit      { LitExpr (None, Dec, $1) }
  | BinLit      { LitExpr (None, Bin, $1) }
  | OctLit      { LitExpr (None, Oct, $1) }
  | HexLit      { LitExpr (None, Hex, $1) }
  | Int DecLit  { LitExpr (Some $1, Dec, $2) }
  | Int BinLit  { LitExpr (Some $1, Bin, $2) }
  | Int OctLit  { LitExpr (Some $1, Oct, $2) }
  | Int HexLit  { LitExpr (Some $1, Hex, $2) }

expr: let_expr { $1 }

atom_expr:
  | Int         { IntExpr $1 }
  | Ident       { IdentExpr $1 }
  | TRUE        { BoolExpr true }
  | FALSE       { BoolExpr false }
  | literal     { $1 }
  | LParen expr RParen { $2 }
  | struct_literal { $1 }
  | UNDEF       { UndefExpr }
  | case_expr   { $1 }
  | concat_expr { $1 }

concat_expr:
  LBrace separated_nonempty_list(Comma, expr) RBrace { ConcatExpr $2 }

case_expr:
  CASE; LParen; e = expr; RParen; branches = list(case_branch); END
    { CaseExpr (e, branches) }

case_branch: separated_nonempty_list(Comma, expr) Colon expr Semi { $1, $3 }

bin_expr:
  | postfix_expr { $1 }
  | bin_expr Plus bin_expr      { BinExpr (Add, $1, $3) }
  | bin_expr Minus bin_expr     { BinExpr (Sub, $1, $3) }
  | bin_expr Equal bin_expr     { BinExpr (S.Eq, $1, $3) }
  | bin_expr NotEqual bin_expr  { BinExpr (NotEq, $1, $3) }
  | bin_expr Amp bin_expr       { BinExpr (LogAnd, $1, $3) }
  | bin_expr Caret bin_expr     { BinExpr (LogXor, $1, $3) }
  | bin_expr Bar bin_expr       { BinExpr (LogOr, $1, $3) }
  | bin_expr And bin_expr       { BinExpr (S.And, $1, $3) }
  | bin_expr Or bin_expr        { BinExpr (S.Or, $1, $3) }

postfix_expr:
  | atom_expr { $1 }
  | e=atom_expr LBrack hi=Int Colon lo=Int RBrack
    { RangeSelectExpr (e, hi, lo) }
  | e=atom_expr LBrack i=Int RBrack
    { BitSelectExpr (e, i) }
  | func_name=Ident LParen args=separated_nonempty_list(Comma, expr) RParen
    { ApplyExpr (func_name, args) }
  | e=atom_expr Dot name=Ident
    { FieldSelectExpr (e, name) }

let_expr:
  | cond_expr { $1 }
  | LET; name = Ident; Eq; value = expr; rest = list(let_expr_rest); IN; body = expr
    { LetExpr ((name, value) :: rest, body) }

cond_expr:
  | bin_expr { $1 }
  | e1=bin_expr Quest e2=expr Colon e3=cond_expr
    { CondExpr (e1, e2, e3) }

field:
  | Ident               { $1, IdentExpr $1 }
  | Ident Colon expr    { $1, $3 }

struct_literal:
  Ident; LBrace; l = separated_nonempty_list(Comma, field); RBrace
    { StructExpr l }

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
  items = list(module_item); END; Semi
    { ModuleDecl { name; ports; items } }

module_item:
  | decl                { DeclItem $1 }
  | val_mod_item        { $1 }
  | inst_mod_item       { $1 }
  | assign_mod_item     { $1 }

val_mod_item:
  VAL type_ separated_nonempty_list(Comma, Ident) Semi
    { ValItem ($2, $3) }

inst_mod_item:
  mod_name = Ident; type_params = loption(delimited(LParen, separated_nonempty_list(Comma, type_), RParen))
  inst_name = Ident; LParen; ports = separated_nonempty_list(Comma, field); RParen; Semi
    { InstItem { mod_name; type_params; inst_name; ports } }

assign_mod_item:
  ASSIGN Ident Eq expr Semi { AssignItem ($2, $4) }
