(** Boolean constraint propagation (BCP) *)

open Base

(** Status of a clause w.r.t. an assignment *)
type status = Sat | Unsat | Unit of Lit.t | Unresolved

val status : Eval.t -> Clause.t -> status
(** [status nu c] returns the status of clause [c] w.r.t. assignment [nu] *)

(** Result of running BCP *)
type result =
  | Unsat of Clause.t  (** at least one clause is unsat *)
  | Unknown  (** no unsat, and at least one clause is unresolved *)
  | Sat  (** no unsat or unresolved *)

val run : int -> Assign.t -> Clause.t list -> result * Assign.t
(** [run i a f] runs BCP on clauses [cs] with assignment [a] at the [i]-th
    decision level. It returns the result and the updated assignment. *)
