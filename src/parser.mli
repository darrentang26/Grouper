type token =
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACKET
  | RBRACKET
  | COLON
  | DOT
  | COMMA
  | PLUS
  | MINUS
  | STAR
  | DIVIDE
  | ASSIGN
  | UNDERSCORE
  | ARROW
  | EQ
  | NEQ
  | LT
  | LEQ
  | GT
  | GEQ
  | AND
  | OR
  | NOT
  | GROUP
  | RING
  | FIELD
  | LET
  | IN
  | LAND
  | IF
  | THEN
  | ELSE
  | END
  | TYPE
  | OF
  | BAR
  | LIST
  | PAIR
  | INT
  | BOOL
  | FLOAT
  | STRING
  | VOID
  | PRINT
  | FUNCTION
  | MATCH
  | WITH
  | LITERAL of (int)
  | BLIT of (bool)
  | NAME of (string)
  | ADTNAME of (string)
  | FLIT of (string)
  | STRINGLIT of (string)
  | EOF

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.program
