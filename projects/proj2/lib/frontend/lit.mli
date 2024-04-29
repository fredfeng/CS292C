(** CNF literal *)

open Base

type t [@@deriving compare, equal, sexp, hash]

val pp : t Fmt.t
(** Pretty-printer *)

val var : t -> Var.t
(** Return the variable of a literal *)

val of_int : int -> t
(** Convert an integer to a literal. Raises [Failure] if the integer is 0 *)

val negate : t -> t
(** Negation *)

val dummy : t
(** Dummy literal (with id 0) *)

val make_pos : Var.t -> t
(** [make_pos v] makes a positive literal with variable [v] *)

val make_neg : Var.t -> t
(** [make_neg v] makes a negative literal with variable [v] *)

val is_pos : t -> bool
(** [is_pos l] is true if [l] is positive *)

val is_neg : t -> bool
(** [is_neg l] is true if [l] is negative *)

include Comparator.S with type t := t
