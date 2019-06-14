let () =
  let lexbuf = Lexing.from_channel stdin in
  try
    let mod_ = Vlog_Parser.top Vlog_Lexer.token lexbuf in
    Format.printf "%a@." Vlog_AST.pp_module mod_
  with Vlog_Parser.Error ->
    let pos = lexbuf.lex_start_p in
    Printf.eprintf "%d:%d: syntax error\n"
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
