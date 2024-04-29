{
open Menhir_parser

exception LexError of string

let failwith msg = raise (LexError msg)

let illegal c =
  failwith (Printf.sprintf "[lexer] unexpected character: '%c'" c)
}


let w = ' ' | '\t'
let newline = "\r\n" | '\r' | '\n'
let num = [ '0'-'9' ]+

rule next_token = parse
  | eof { EOF }
  | w+
    { next_token lexbuf }
  | newline
    { Lexing.new_line lexbuf; next_token lexbuf }
  
  (* begin comment *)
  | 'c'
    { comment lexbuf }

  | "p"
    { P }

  | "cnf"
    { CNF }

  | '0'
    { ZERO }

  | num as n
    { NUM (int_of_string n) }

  | '-'
    { MINUS }

  | '0'
    { ZERO }

  | '%'
    { PERCENT }

  (* no match? raise exception *)
  | _ as c 
    { illegal c }


(* comments start with 'c' and end with a newline *)
and comment = parse
  | newline
    { Lexing.new_line lexbuf; next_token lexbuf }
  | eof
    { EOF }
  | _
    { comment lexbuf }