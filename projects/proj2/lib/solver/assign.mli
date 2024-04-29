(** Variable / literal assignment *)

exception Unassigned

open Base

(** Map variables to their levels *)
module Delta : sig
  type t

  val empty : t
  val pp : t Fmt.t
end

(** Trail of decision and implications at a level *)
module Trail : sig
  type t = { decision : Lit.t; implied : Lit.t list }

  val pp : t Fmt.t
end

(** Map each level to the decision & implication trail *)
module Trails : sig
  type t

  val pp : t Fmt.t
  val empty : t
end

(** Map each implied literal to its antecedent clause (due to unit propagation).
    This is equivalent to the implication graph data structure. *)
module Imp : sig
  type t

  val pp : t Fmt.t
  val empty : t
end

type t = {
  nu : Eval.t;  (** variable map *)
  delta : int Map.M(Var).t;  (** variable decision levels *)
  trails : Trails.t;  (** decision and implication trails *)
  imp : Imp.t;  (** implication graph *)
}
(** Assignment data structure *)

val pp : t Fmt.t
(** Pretty-print an assignment *)

val empty : t
(** Empty assignment *)

val is_assigned : t -> Var.t -> bool
(** Check if a variable is assigned *)

val antecedent : t -> Lit.t -> Clause.t option
(** [antecedent a l] returns [Some c] that [l] was implied by [c]. Otherwise, it
    returns [None] (i.e., when [l] is a decision literal) *)

val assign_decision : t -> int -> Lit.t -> t
(** [assign_decision a level l] assigns decision literal [l] to true at the
    given level *)

val assign_implied : t -> int -> Clause.t -> Lit.t -> t
(** [assign_implied a level c l] assigns implied literal [l] to true at [level]
    and records that it was implied by clause [c] *)

val level_exn : t -> Lit.t -> int
(** [level_exn a l] returns the decision level at which [l] or [Lit.negate l]
    was assigned, if at all, and raises [Unassigned] otherwise *)

val trail_exn : t -> int -> Trail.t
(** [trail_exn a l] returns the trail of implication at the given level or
    raises [Unassigned] if [l] is not in the assignment *)

val pp_clause_with_level : t -> Clause.t Fmt.t
(** [pp_clause_with_level a] is a pretty-printer for a clause [c] such that each
    literal is annotated by its level in [a] *)

val pp_clause_with_value : t -> Clause.t Fmt.t
(** [pp_clause_with_value a] is a pretty-printer for a clause [c] such that each
    literal is annotated by its truth-value according to [a] *)

val invariant : int -> level:int -> t -> unit
(** [invariant n ~level a] checks that the assignment is consistent up to level
    [level] *)
