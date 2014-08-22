type token =
  | NEWLINE
  | COMMA
  | IF
  | DOT
  | QUERY
  | ID of (string)
  | VAR of (string)
  | LPARAN
  | RPARAN

val input :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit
