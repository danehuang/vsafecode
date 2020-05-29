let parse_file() =
  let argv = Sys.argv in
  let _ =
    if Array.length argv != 2
    then (prerr_string ("usage: " ^ argv.(0) ^ " [file-to-parse]\n");
    exit 1) in
  let ch = open_in argv.(1) in
  Parse.program Lex.lexer (Lexing.from_channel ch)

let parse_stdin() =
  Parse.program Lex.lexer (Lexing.from_channel stdin)

(* Expect 1 command line argument, the file to interpret
 * usage: ppool [file-to-interpret] *)
let _ =
  let prog = parse_file() in
  print_endline (Ast.string_of_fpooltyps prog) 
