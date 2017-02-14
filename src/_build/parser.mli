
(* The type of tokens. *)

type token = 
  | WITH
  | WHERE
  | TYPE
  | TAG of (string * Lexing.position * Lexing.position)
  | SEMI
  | RPAR
  | RETURN
  | REC
  | RBRACKET
  | RBRACE
  | PROGRAM
  | MATCH
  | LPAR
  | LET
  | LBRACKET
  | LBRACE
  | IN
  | IDENTIFIER of (string * Lexing.position * Lexing.position)
  | FUN
  | FORALL
  | FIX
  | EQ
  | EOF
  | END
  | DOT
  | DATA
  | CONSTRUCTOR
  | COLON
  | BAR
  | ARROW
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.program)
