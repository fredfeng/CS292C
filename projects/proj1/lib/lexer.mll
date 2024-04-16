{
open Menhir_parser

exception LexError of string

let[@inline] failwith msg = raise (LexError msg)

let[@inline] illegal c =
  failwith (Printf.sprintf "[lexer] unexpected character: '%c'" c)
}

(* regular expressions *)
let whitespace = ' ' | '\t'
let newline = "\r\n" | '\r' | '\n'
let digit = ['0'-'9']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*


rule next_token = parse
  | eof { EOF }
  | whitespace+
    { next_token lexbuf }
  | newline
    { Lexing.new_line lexbuf; next_token lexbuf }
  | "//"
    { comment lexbuf }

  (* arith *)
  | '+' { PLUS }
  | '-' { MINUS }
  | '*' { TIMES }
  | '/' { DIV }
  | '%' { MOD }

  (* bool *)
  | "!"   { NOT }
  | "&&"  { AND }
  | "||"  { OR }
  | "==>" { IMPLY }
  | "<==>" { IFF }
  | "true" { TRUE }
  | "false" { FALSE }

  (* comparison *)
  | "==" { EQ }
  | "!=" { NEQ }
  | "<"  { LT }
  | "<=" { LEQ }
  | ">"  { GT }
  | ">=" { GEQ }

  (* commands *)
  | ":="   { ASSIGN }
  | "if"   { IF }
  | "else" { ELSE }
  | "while"     { WHILE }
  | "invariant" { INVARIANT }
  | "assume" { ASSUMES }
  | "assert" { ASSERTS }
  | "print"  { PRINT }

  (* program *)
  | "method" { METHOD }
  | "var"    { VAR }
  | "requires" { REQUIRES }
  | "ensures"  { ENSURES }
  | "return"      { RET }
  | "returns"   { RETURNS }

  (* formula *)
  | "forall" { FORALL }
  | "exists" { EXISTS }
  
  (* types *)
  | "int"   { TINT }
  | "array" { TARRAY }

  (* misc *)
  | ':' { COLON }
  | ',' { COMMA }
  | ';' { SEMI }
  | '(' { LPAR }
  | ')' { RPAR }
  | '[' { LBRAC }
  | ']' { RBRAC }
  | '{' { LCURLY }
  | '}' { RCURLY }
  
  (* literals *)
  | digit+ as num
    { NUM (int_of_string num) }
  | ident as x { ID x }

  (* no match? raise exception *)
  | _ as c { illegal c }


(* allow C-style comments prefixed with // *)
and comment = parse
  | newline
    { Lexing.new_line lexbuf; next_token lexbuf }
  | eof
    { EOF }
  | _
    { comment lexbuf }

