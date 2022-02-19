(* Ocamllex scanner for MicroC *)

{ open Parser }

let digit = ['0' - '9']
let digits = digit+

rule token = parse
  [' ' '\t' '\r' '\n'] { token lexbuf } (* Whitespace *)
| "(*"     { comment lexbuf }           (* Block comments *)
| "//"     { lcomment lexbuf }          (* One line comments *)
| '('      { LPAREN }
| ')'      { RPAREN }
| '{'      { LBRACE }
| '}'      { RBRACE }
| '['      { LBRACKET }
| ']'      { RBRACKET }
| '@'      { decorator lexbuf }
| ':'      { COLON }
| '.'      { DOT }
| ','      { COMMA }
| '+'      { PLUS }
| '-'      { MINUS }
| '*'      { STAR }
| '/'      { DIVIDE }
| '='      { ASSIGN }
| "->"     { ARROW }
| "=="     { EQ }
| "!="     { NEQ }
| '<'      { LT }
| "<="     { LEQ }
| ">"      { GT }
| ">="     { GEQ }
| "&&"     { AND }
| "||"     { OR }
| "!"      { NOT }
| "group"  { GROUP }
| "ring"   { RING }
| "field"  { FIELD }
| "let"    { LET }
| "in"     { IN }
| "and"    { LAND }
| "if"     { IF }
| "then"   { THEN }
| "else"   { ELSE }
| "end"    { END }
| "type"   { TYPE }
| "of"     { OF }
| '|'      { BAR }
| "list"   { LIST }
| "pair"   { PAIR }
| "int"    { INT }
| "bool"   { BOOL }
| "float"  { FLOAT }
| "string" { STRING }
| "true"   { BLIT(true)  }
| "false"  { BLIT(false) }
| digits as lxm { LITERAL(int_of_string lxm) }
| digits '.' digit* as lxm { FLIT(lxm) }
| '"' _ '"' as lxm { STRINGLIT(lxm) }
| ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm { NAME(lxm) }
| eof { EOF }
| _ as char { raise (Failure("illegal character " ^ Char.escaped char)) }

and comment = parse
  "*)" { token lexbuf }
| _    { comment lexbuf }

and lcomment = parse
  '\n' { token lexbuf }
| _    { lcomment lexbuf }

and decorator = parse
  [' ' '\t' '\r'] { decorator lexbuf }
| '\n' { token lexbuf }
| "overload"  { OVERLOAD }
| "types"     { TYPES }
| '*'         { STAR }
| "->"        { ARROW }
| ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm { NAME(lxm) }
