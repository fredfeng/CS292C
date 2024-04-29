(** Proof tree

    A proof tree is either a known fact, or a use of the resolution rule applied
    to two proof trees *)

open Base

type t
(** Type of proof trees *)

val pp : t Fmt.t
(** Pretty printer *)

val replay : t -> Clause.t
(** Replay a proof and return the resulting clause *)

val fact : Clause.t -> t
(** Construct a proof tree consisting of a single fact *)

val resolve : left:t -> on:Lit.t -> right:t -> t
(** [resolve ~left ~on ~right] constructs a proof tree by resolving proofs
    [left] and [right] on a literal [on]. Requires [on] to be a literal in
    [left] and the negation of [on] to be a literal in [right]. *)

val validate : Set.M(Clause).t -> t -> Clause.t
(** Given a set of assumptions [cs], [validate cs p] checks that the proof tree
    [p] is well-formed, i.e., every fact is an assumption *)

val is_refutation : Set.M(Clause).t -> t -> bool
(** Given a set of assumptions [cs], [is_refutation cs p] checks that a
    well-formed proof is a refutation proof. I.e., [validate cs p] returns the
    empty clause. *)

val facts : t -> Set.M(Clause).t
(** Return the set of facts used in the proof tree *)
