{
open Lexing
open Simplog_Parser

exception Error of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = pos.pos_cnum;
      pos_lnum = pos.pos_lnum + 1 }

let convert_bin_literal s =
  Z.of_string_base 2 s

let convert_oct_literal s =
  Z.of_string_base 8 s

let convert_hex_literal s =
  Z.of_string_base 16 s

let convert_dec_literal s =
  Z.of_string_base 10 s

}

let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '$']*

let white = [' ' '\t']+
let single_line_comment = "//" [^'\n']* '\n'

(* numeric literals *)

let base_prefix = "'"
let dec_base = base_prefix ['d' 'D']
let bin_base = base_prefix ['b' 'B']
let oct_base = base_prefix ['o' 'O']
let hex_base = base_prefix ['h' 'H']

let bin_digit = ['0' '1']
let oct_digit = ['0'-'7']
let dec_digit = ['0'-'9']
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']

let dec_number = dec_digit (dec_digit|'_')*
let bin_number = bin_digit (bin_digit|'_')*
let oct_number = oct_digit (oct_digit|'_')*
let hex_number = hex_digit (hex_digit|'_')*

rule token = parse
  | white               { token lexbuf }
  | single_line_comment { next_line lexbuf; token lexbuf }
  | "/*"                { comment lexbuf }
  | '\n'                { next_line lexbuf; token lexbuf }

  (* numeric literals *)
  | dec_base (dec_number as s) { DecLit (convert_dec_literal s) }
  | bin_base (bin_number as s) { BinLit (convert_bin_literal s) }
  | oct_base (oct_number as s) { OctLit (convert_oct_literal s) }
  | hex_base (hex_number as s) { HexLit (convert_hex_literal s) }
  | dec_number as s { Int (int_of_string s) }

  (* keywords *)
  | "and"               { AND }
  | "assign"            { ASSIGN }
  | "bits"              { BITS }
  | "bool"              { BOOL }
  | "case"              { CASE }
  | "default"           { DEFAULT }
  | "end"               { END }
  | "enum"              { ENUM }
  | "false"             { FALSE }
  | "function"          { FUNCTION }
  | "import"            { IMPORT }
  | "in"                { IN }
  | "input"             { INPUT }
  | "let"               { LET }
  | "module"            { MODULE }
  | "output"            { OUTPUT }
  | "pack"              { PACK }
  | "reg"               { REG }
  | "signed"            { SIGNED }
  | "struct"            { STRUCT }
  | "true"              { TRUE }
  | "typedef"           { TYPEDEF }
  | "undef"             { UNDEF }
  | "unpack"            { UNPACK }
(*| "unsigned"          { UNSIGNED }*)
  | "val"               { VAL }

  | ident as s          { Ident s }
  | "&&"                { And }
  | "||"                { Or }
  | "=="                { Equal }
  | "!="                { NotEqual }
  | "<="                { LE }
  | ">="                { GE }
  | "<<"                { SHL }
  | ">>"                { SHR }
  | ">>>"               { ASHR }
  | '!'                 { Bang }
  | '&'                 { Amp }
  | '('                 { LParen }
  | ')'                 { RParen }
  | '*'                 { Star }
  | '+'                 { Plus }
  | ','                 { Comma }
  | '-'                 { Minus }
  | '.'                 { Dot }
  | ':'                 { Colon }
  | ';'                 { Semi }
  | '<'                 { LT }
  | '='                 { Eq }
  | '>'                 { GT }
  | '?'                 { Quest }
  | '['                 { LBrack }
  | ']'                 { RBrack }
  | '^'                 { Caret }
  | '{'                 { LBrace }
  | '|'                 { Bar }
  | '}'                 { RBrace }
  | '~'                 { Tilde }
  | eof                 { EOF }

  | '"' ([^'"' '\n']* as s) '"' { String s }

  | _ as c { raise (Error (Printf.sprintf "unexpected character: %c" c)) }

and comment = parse
  | "*/"                { token lexbuf }
  | '\n'                { next_line lexbuf; comment lexbuf }
  | _                   { comment lexbuf }
