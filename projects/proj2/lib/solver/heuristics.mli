(** Variable selection heuristics.

    Currently support:
    - random
    - VSIDS (Variable State Independent Decaying Sum) *)

open Base

type score
(** A score predicts how "good" a literal is in decisions *)

type t
(** A heuristics is a mutable map that associates each literal with a score *)

val pp : t Fmt.t
(** Pretty printer for heuristics *)

val empty : unit -> t
(** Create an empty heuristics *)

val init : Formula.t -> t -> unit
(** Initialize the heuristics given the input formula *)

val record_conflict : t -> Clause.t -> unit
(** Update the heuristics after a conflict *)

val next_unassigned : Set.M(Var).t -> Assign.t -> Var.t option
(** Return the next unassigned variable (ordered by variable ID) *)

val random_unassigned : Set.M(Var).t -> Assign.t -> Lit.t option
(** Return a random unassigned literal *)

val best_unassigned : Set.M(Var).t -> Assign.t -> t -> Lit.t option
(** Return the best unassigned variable according to the heuristics *)
