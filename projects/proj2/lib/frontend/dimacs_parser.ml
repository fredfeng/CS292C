(** Parser for CNF problems in DIMACS format *)

include Nice_parser.Make (struct
  type result = Description.t
  type token = Menhir_parser.token

  exception ParseError = Menhir_parser.Error

  let parse = Menhir_parser.description

  include Scanner
end)
