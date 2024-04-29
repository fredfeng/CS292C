exception Solver_error

module Make : functor
  (_ : sig
     val desc : Description.t
   end)
  -> sig
  val analyze : int -> Assign.t -> Clause.t -> Clause.t * Proof.t * int
  val solve : State.t -> State.t
  val result : Solution.t
end

val run : Description.t -> Solution.t
