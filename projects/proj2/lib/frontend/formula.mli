(** CNF formula *)

open Base

type t = Clause.t list [@@deriving compare, equal]

val pp : t Fmt.t
(** Pretty printer *)

val vars : t -> Set.M(Var).t
(** The set of variables in a formula *)

val of_ints : int list list -> t
(** Convert a 2d int list into a formula *)
