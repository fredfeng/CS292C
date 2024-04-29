exception Solver_error

module Make : functor
  (_ : sig
     val desc : Description.t
   end)
  -> sig
  val make_proof : Assign.t -> Clause.t -> Proof.t
  val solve : State.t -> State.t
  val result : Solution.t
end

val run : Description.t -> Solution.t
