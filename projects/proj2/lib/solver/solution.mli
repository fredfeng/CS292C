(** Solution to a CNF problem *)

type t = SATISFIABLE of Eval.t | UNSATISFIABLE of Script.t

val pp : t Fmt.t
(** Pretty-printer for the solution *)

val pp_short : t Fmt.t
(** Short pretty-printer for the solution *)

val verify : Description.t -> t -> unit
(** Verify the solution *)

val verify_sat : Description.t -> t -> unit
(** Verify the solution if it is SATISFIABLE *)

val verify_unsat : Description.t -> t -> unit
(** Verify the solution if it is UNSATISFIABLE *)

val is_sat : t -> bool
(** Check if the solution is SATISFIABLE *)

val is_unsat : t -> bool
(** Check if the solution is UNSATISFIABLE *)
