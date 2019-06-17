open ExtLib
open Util

module M = Map.Make(String_Key)
module H = Hashtbl.Make(String_Key)
module G = Graph.Imperative.Digraph.Concrete(String_Key)

exception Syntax_Error

let parse_file filepath =
  let ic = open_in filepath in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filepath };
  try
    let decls = Simplog_Parser.top Simplog_Lexer.token lexbuf in
    close_in ic;
    decls
  with Simplog_Lexer.Error _ | Simplog_Parser.Error ->
    let pos = lexbuf.lex_start_p in
    Printf.eprintf "%s:%d:%d: syntax error\n"
      pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
    close_in ic;
    raise Syntax_Error

let module_name_from_filepath fpath =
  let fname = Filename.basename fpath in
  let stem = Filename.remove_extension fname in
  stem

(* obtain module file path from module name *)
let find_module mod_name =
  mod_name ^ ".sl"

let rec read_module dep_graph cache mod_name mod_fpath =
  (*Printf.eprintf "reading module %s\n" mod_name;*)
  let imports, decls = parse_file mod_fpath in
  H.add cache mod_name decls;
  G.add_vertex dep_graph mod_name;
  imports |> List.iter begin fun (import_type_opt, imported_mod_names) ->
    match import_type_opt with
    | None ->
      imported_mod_names |> List.iter begin fun imported_mod_name ->
        (* add edge to dependency graph *)
        G.add_edge dep_graph imported_mod_name mod_name;
        (* load the module if not already loaded *)
        if not (H.mem cache imported_mod_name) then
          read_module dep_graph cache imported_mod_name
            (find_module imported_mod_name)
      end
    | Some _ -> ()
  end

let read_toplevel mod_name fpath =
  let cache = H.create 1 in
  let dep_graph = G.create () in
  read_module dep_graph cache mod_name fpath;
  let module Topo = Graph.Topological.Make(G) in
  let decls = ref [] in
  Topo.iter (fun m -> (*Printf.eprintf "%s\n" m;*) decls := H.find cache m :: !decls) dep_graph;
  !decls |> List.rev |> List.concat

let () =
  let fpath = Sys.argv.(1) in
  let top_module_name = module_name_from_filepath fpath in
  let decls =
    try read_toplevel top_module_name fpath with Syntax_Error -> exit 1
  in
  let env, typed_decls =
    try Typing.type_decls decls with Typing.Error -> exit 1
  in
  Translate_Isa.output_theory top_module_name env typed_decls
