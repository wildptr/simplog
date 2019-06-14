{
open Lexing
open Vlog_Parser
open Big_int

exception Error of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = pos.pos_cnum;
      pos_lnum = pos.pos_lnum + 1 }

module M = Map.Make(String)

let keyword_map =
  [
    "always", ALWAYS;
    "assign", ASSIGN;
    "begin", BEGIN;
    "case", CASE;
    "casex", CASEX;
    "casez", CASEZ;
    "default", DEFAULT;
    "else", ELSE;
    "end", END;
    "endcase", ENDCASE;
    "endmodule", ENDMODULE;
    "if", IF;
    "inout", INOUT;
    "input", INPUT;
    "localparam", LOCALPARAM;
    "module", MODULE;
    "negedge", NEGEDGE;
    "output", OUTPUT;
    "parameter", PARAMETER;
    "posedge", POSEDGE;
    "reg", REG;
    "wire", WIRE;
  ]
  |> List.to_seq |> M.of_seq

let replace_xz s =
  let n = String.length s in
  let b = Bytes.create n in
  for i=0 to n-1 do
    let c =
      match s.[i] with
      | 'x' | 'X' | 'z' | 'Z' -> '0'
      | c -> c
    in
    Bytes.set b i c
  done;
  Bytes.to_string b

let convert_bin_literal s =
  Z.of_string ("0b" ^ (replace_xz s))

let convert_oct_literal s =
  Z.of_string ("0o" ^ (replace_xz s))

let convert_hex_literal s =
  Z.of_string ("0x" ^ (replace_xz s))

let convert_dec_literal s =
  Z.of_string (replace_xz s)

}

(* numeric literals *)

let base_prefix = "'" ['s' 'S']?
let dec_base = base_prefix ['d' 'D']
let bin_base = base_prefix ['b' 'B']
let oct_base = base_prefix ['o' 'O']
let hex_base = base_prefix ['h' 'H']

let xz_digit = ['x' 'X' 'z' 'Z' '?']
let bin_digit = ['0' '1']
let bin_digit' = bin_digit | xz_digit
let oct_digit = ['0'-'7']
let oct_digit' = oct_digit | xz_digit
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let hex_digit' = hex_digit | xz_digit

let dec_number = ['0'-'9'] ['0'-'9' '_']*
let bin_number' = bin_digit' (bin_digit'|'_')*
let oct_number' = oct_digit' (oct_digit'|'_')*
let hex_number' = hex_digit' (hex_digit'|'_')*

(* identifiers *)

let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '$']*

let white_char = [' ' '\t']
let white = white_char+
let single_line_comment = "//" [^'\n']* '\n'

rule token = parse
  | white { token lexbuf }
  | single_line_comment { next_line lexbuf; token lexbuf }
  | "/*" { comment lexbuf }
  | '\n' { next_line lexbuf; token lexbuf }
  | dec_base white_char* (dec_number as value)
    { DecLit (convert_dec_literal value) }
  | bin_base white_char* (bin_number' as value)
    { BinLit (convert_bin_literal value) }
  | oct_base white_char* (oct_number' as value)
    { OctLit (convert_oct_literal value) }
  | hex_base white_char* (hex_number' as value)
    { HexLit (convert_hex_literal value) }
  | ident as s
    { match M.find_opt s keyword_map with Some k -> k | None -> Ident s }
  | dec_number as s { Int (int_of_string s) }
  | "!=" { BangEq }
  | "+:" { PlusColon }
  | "<<" { LtLt }
  | "<=" { LtEq }
  | "==" { EqEq }
  | ">=" { GtEq }
  | ">>" { GtGt }
  | '!' { Bang }
  | '#' { Hash }
  | '&' { Amp }
  | '(' { LParen }
  | ')' { RParen }
  | '*' { Star }
  | '+' { Plus }
  | ',' { Comma }
  | '-' { Minus }
  | '.' { Dot }
  | ':' { Colon }
  | ';' { Semi }
  | '<' { Lt }
  | '=' { Eq }
  | '>' { Gt }
  | '?' { Quest }
  | '@' { At }
  | '[' { LBrack }
  | ']' { RBrack }
  | '^' { Caret }
  | '{' { LBrace }
  | '|' { Bar }
  | '}' { RBrace }
  | '~' { Tilde }
  | eof { EOF }
  | _ as c { raise (Error (Printf.sprintf "unexpected character: %c" c)) }

and comment = parse
  | "*/" { token lexbuf }
  | '\n' { next_line lexbuf; comment lexbuf }
  | _ { comment lexbuf }
