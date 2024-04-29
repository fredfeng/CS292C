(** CNF variable *)

type t [@@deriving sexp, hash]
(** Type for representing variables *)

val compare : t -> t -> int
(** Compare two variables *)

val equal : t -> t -> bool
(** Check if two variables are equal *)

val of_int : int -> t
(** Convert an integer to a variable *)

val id : t -> int
(** Return the integer id of a variable *)

val dummy : t
(** Dummy variable with id 0 *)

val pp : t Fmt.t

include Base.Comparator.S with type t := t
