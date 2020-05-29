%{
open Ast
open Lexing

let rhs n = 
  let pos = Parsing.rhs_start_pos n in
  pos.pos_lnum
let parse_error s =
  let pos = Parsing.symbol_end_pos () in
  let l = pos.pos_lnum in
  let c = pos.pos_cnum in
  print_string ("line "^(string_of_int l)^" at char " ^(string_of_int c)^": "^s^"\n")
%}

%start program

%type <Ast.fpooltyps> program

%token COMMA LPAREN RPAREN LBRACKET RBRACKET LCURLY RCURLY LANGLE RANGLE BY STAR EOL FLOAT COLON POUND VOID
%token <int> INT
%token <string> ID
%token EOF

%%

program :
  fpooltyps EOF { $1 }

fpooltyps :
  fpooltyp { [$1] }
| fpooltyp fpooltyps { $1::$2 }

fpooltyp :
  ID LPAREN ID RPAREN LPAREN ids RPAREN LCURLY pooltyps RCURLY { ($1, $9, ($3::$6)) }
| ID LPAREN ID RPAREN LPAREN RPAREN LCURLY pooltyps RCURLY { ($1, $8, [$3]) }
| ID LPAREN ID RPAREN LPAREN RPAREN LCURLY RCURLY { ($1, [], [$3]) }
| ID LPAREN ID RPAREN LPAREN ids RPAREN LCURLY RCURLY { ($1, [], ($3::$6)) }

pooltyps : 
  pooltyp { [$1] }
| pooltyp pooltyps { $1::$2 }

pooltyp :
  ID LANGLE typs RANGLE COLON ids POUND { ($1, $6, $3) }
| ID LANGLE typs RANGLE COLON POUND { ($1, [], $3) }
| ID LANGLE RANGLE COLON POUND { ($1, [], []) }
| ID LANGLE RANGLE COLON ids POUND { ($1, $5, []) }

ids :
  ID { [$1] }
| ID COMMA ids { $1::$3 }

typs :
  typ { [$1] }
| typ COMMA typs { $1::$3 }

typ :
  FLOAT { Ast.Typ_float }
| INT { Ast.Typ_int($1 - 1) }
| ID { Ast.Typ_name($1, []) }
| typ STAR { Ast.Typ_ptr($1, "tmp") }
| VOID LPAREN typs RPAREN { Ast.Typ_fun([], $3, None) }
| typ LPAREN typs RPAREN { Ast.Typ_fun([], $3, Some $1) }

/*
| LBPAREN INT TIMES typ RBPAREN { Ast.Typ_array($2, $4) }
| typ LPAREN typs RPAREN { Ast.Typ_fun($1, $3) }
| LCPAREN typs LRPAREN { Ast.Typ_struct($1, 
*/
