(** Interpreter *)

val pp_u : bool option Fmt.t
(** Pretty printer for potentially undetermined boolean values *)

type t [@@deriving compare, equal]
(** Variable map *)

val pp : t Fmt.t
(** Pretty printer *)

val empty : t
(** The empty mapping *)

val set : t -> Var.t -> bool -> t
(** [set nu var b] returns a new mapping where [var] is assigned to [b] *)

val is_assigned : t -> Var.t -> bool
(** [is_assigned nu var] returns true if [var] is assigned in [nu] *)

val var : t -> Var.t -> bool option
(** [var nu x] evaluates the variable [x] under the assignment [nu] *)

val lit : t -> Lit.t -> bool option
(** [lit nu l] evaluates the literal [l] under the assignment [nu] *)

val clause : t -> Clause.t -> bool
(** [clause nu c] evaluates the clause [c] under the assignment [nu] *)

val formula : t -> Formula.t -> bool
(** [formula nu f] evaluates the formula [f] under the assignment [nu] *)
