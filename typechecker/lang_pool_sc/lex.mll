{
open Parse
open Lexing

let debug = ref false
let log str = 
  if !debug then print_endline str else ()

let incr_lineno lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with
    pos_lnum = pos.pos_lnum + 1;
    pos_bol = pos.pos_cnum;
  }
}

let cr='\013'
let nl='\010'
let eol=(cr nl|nl|cr)
let ws=('\012'|'\t'|' ')*
let digit=['0'-'9']
let hex=['0'-'9''A'-'F''a'-'f']

let id = ['A'-'Z''a'-'z''_''.''%''\x01']['.''a'-'z''A'-'Z''0'-'9''_']*

rule lexer = parse
| eol { incr_lineno lexbuf; lexer lexbuf }
| ws+ { lexer lexbuf }
| ',' { log "comma"; COMMA }
| '(' { log "lparen"; LPAREN }
| ')' { log "rparen"; RPAREN }
| '[' { log "lbracket"; LBRACKET }
| ']' { log "rbracket"; RBRACKET }
| '{' { log "lcurly"; LCURLY }
| '}' { log "rcurly"; RCURLY }
| '<' { log "langle"; LANGLE }
| '>' { log "rangle"; RANGLE }
| 'x' { log "by"; BY }
| '*' { log "star"; STAR }
| ':' { log "colon"; COLON }
| '#' { log "pound"; POUND }
| "float" { log "float"; FLOAT } 
| "void" { log "void"; VOID }
| 'i'digit+ { let str = Lexing.lexeme lexbuf in
		log str ;
		INT(int_of_string(String.sub str 1 (String.length str - 1))) }
| id { log (Lexing.lexeme lexbuf); ID(Lexing.lexeme lexbuf) }
| eof { EOF }
