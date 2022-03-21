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
| ':'      { COLON }
| '.'      { DOT }
| ','      { COMMA }
| '+'      { PLUS }
| '-'      { MINUS }
| '*'      { STAR }
| '/'      { DIVIDE }
| "mod"    { MOD }
| "::"     { CONS }
| '='      { ASSIGN }
| '_'      { UNDERSCORE }
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
| "::"     { CONS }
| "group"  { GROUP }
| "ring"   { RING }
| "field"  { FIELD }
| "poly"   { POLY }
| "let"    { LET }
| "in"     { IN }
| "and"    { LAND }
| "if"     { IF }
| "then"   { THEN }
| "else"   { ELSE }
| "type"   { TYPE }
| '*'      { STAR }
| "->"     { ARROW }
| "of"     { OF }
| '|'      { BAR }
| "list"   { LIST }
| "Int"    { INT }
| "Bool"   { BOOL }
| "Float"  { FLOAT }
| "String" { STRING }
| "print"  { PRINT }
| "true"   { BLIT(true)  }
| "false"  { BLIT(false) }
| "lambda" { FUNCTION }
| "match"  { MATCH }
| "with"   { WITH }
| "end"    { END }
| digits as lxm { LITERAL(int_of_string lxm) }
| digits '.' digit* as lxm { FLIT(lxm) }
| '\"' [^'\"']* '\"' as lxm { STRINGLIT((String.sub lxm 1 ((String.length lxm) - 2))) }
| ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm { NAME(lxm) }
| ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* as lxm { TYPNAME(lxm) }
| ['A'-'Z']['A'-'Z']* as lxm { ADTNAME(lxm) }
| eof { EOF }
| _ as char { raise (Failure("illegal character " ^ Char.escaped char)) }

and comment = parse
  "*)" { token lexbuf }
| _    { comment lexbuf }

and lcomment = parse
  '\n' { token lexbuf }
| _    { lcomment lexbuf }
