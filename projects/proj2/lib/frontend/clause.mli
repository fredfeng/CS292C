(** CNF clause *)

open Base

type t = Set.M(Lit).t [@@deriving compare, equal, sexp, hash]
(** A clause is a disjunction of literals, represented as a set *)

val pp : t Fmt.t
(** Pretty-printer for clauses *)

val vars : t -> Set.M(Var).t
(** The set of variables in a clause *)

val of_int_list : int list -> t
(** Convert an list of integers to a clause *)

val contains : t -> Lit.t -> bool
(** [contains c l] returns [true] if literal [l] is in [c] *)

val resolve : t -> Lit.t -> t -> t option
(** [resolve c1 l c2] returns the resolvent of [c1] and [c2] with respect to
    [l]. *)

val resolve_exn : t -> Lit.t -> t -> t
(** [resolve_exn c1 l c2] is like [resolve c1 l c2] but it raises an exception
    if resolution fails, i.e., when [l] not in [c1] or [negate l] not in [c2] *)

val empty : t
(** The empty clause *)

include Comparator.S with type t := t
