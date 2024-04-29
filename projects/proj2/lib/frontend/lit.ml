open Base

(** Sign *)
module Sign = struct
  type t = Neg | Pos [@@deriving compare, equal, variants, sexp, hash]

  let pp = Fmt.using (function Pos -> "+" | Neg -> "-") Fmt.string
  let negate = function Pos -> Neg | Neg -> Pos
end

type t = Lit of Sign.t * Var.t [@@deriving compare, equal, sexp, hash]

let of_int n =
  if n > 0 then Lit (Sign.Pos, Var.of_int n)
  else if n < 0 then Lit (Neg, Var.of_int (-n))
  else (
    Logs.err (fun m -> m "Invalid literal: %d" n);
    failwith "of_int")

let var (Lit (_, v)) : Var.t = v
let sign (Lit (s, _)) : Sign.t = s
let pp ppf (Lit (s, v)) = Fmt.pf ppf "%a%a" Sign.pp s Var.pp v
let with_sign s v = Lit (s, v)
let make_pos = with_sign Sign.Pos
let make_neg = with_sign Sign.Neg
let negate (Lit (s, v)) : t = Lit (Sign.negate s, v)
let dummy = Lit (Sign.Pos, Var.dummy)
let is_pos (Lit (s, _)) = Sign.equal s Sign.Pos
let is_neg (Lit (s, _)) = Sign.equal s Sign.Neg

include (val Comparator.make ~compare ~sexp_of_t)
