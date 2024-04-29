(** Description of a CNF problem *)

type t = { num_vars : int; num_clauses : int; f : Formula.t }
