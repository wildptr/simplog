let () =
  let lexbuf = Lexing.from_channel stdin in
  try
    let _ = Simplog_Parser.top Simplog_Lexer.token lexbuf in
    ()
  with Simplog_Parser.Error ->
    let pos = lexbuf.lex_start_p in
    Printf.eprintf "%d:%d: syntax error\n"
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
