(** Solver state *)

type t = {
  level : int;  (** current decision level *)
  decision : Lit.t option;  (** current decision literal *)
  a : Assign.t;  (** assignment *)
  h : Heuristics.t;  (** heuristics *)
}

val pp : t Fmt.t
(** Pretty printer *)

val invariant : int -> t -> unit
(** Check state invariant *)

val init_level : int
(** Initial level *)

val init : t
(** Initial state *)

val decide : t -> Lit.t -> t
(** [decide s l] makes a decision [l] at level [s.level + 1], and returns the
    new state *)
