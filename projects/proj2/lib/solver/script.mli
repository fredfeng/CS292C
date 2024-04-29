(** Proof script

    A proof script is a sequence of lemmas, followed by a main proof. Subsequent
    proofs can use previous lemmas. *)

open Base

(** A lemma consists of the statement of the goal, and a proof for the goal *)
module Lemma : sig
  type t
  (** Type of lemmas *)

  val pp : t Fmt.t
  (** Pretty-printer for lemmas *)

  val make : Clause.t -> Proof.t -> t
  (** [make c p] constructs a lemma with goal [c] and proof [p] *)
end

type t
(** Type of proof scripts *)

val pp : t Fmt.t
(** Pretty-printer for proof scripts *)

val make : Lemma.t list -> Proof.t -> t
(** [make ls p] constructs a proof script consisting of lemmas [ls] and main
    proof [p] *)

val validate : Set.M(Clause).t -> t -> Set.M(Lit).t
(** Given a set of assumptions [cs], [validate cs s] checks that the proof
    script [p] is well-formed, i.e., every fact is either an assumption, or a
    previously proven lemma *)

val is_refutation : Set.M(Clause).t -> t -> bool
(** Given a set of assumptions [cs], [is_refutation cs s] checks that a
    well-formed script is a refutation proof. I.e., [validate cs s] returns the
    empty clause. *)
