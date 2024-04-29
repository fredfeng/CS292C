open Base

type t = Var of int [@@deriving compare, equal, sexp, hash]

let of_int n =
  if n > 0 then Var n
  else (
    Logs.err (fun m -> m "Invalid variable: %d" n);
    failwith "of_int")

let id (Var n) = n
let pp = Fmt.using id Fmt.int
let dummy = Var 0

include (val Comparator.make ~compare ~sexp_of_t)
