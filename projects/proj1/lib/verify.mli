open Lang

module Make : functor
  (_ : sig
     val prog : prog
     val meth : meth
   end)
  -> sig
  val gamma_ref : (string * ty) list ref
  val gamma : unit -> (string * ty) list
  val add_gamma : string -> ty -> unit
  val counter : int ref
  val fresh_var : ty -> hint:string -> string
  val modified : stmt -> string list
  val modified_block : block -> string list
  val compile : stmt -> gcom list
  val compile_block : block -> gcom list
  val wp : gcom -> formula -> formula
  val wp_seq : gcom list -> formula -> formula
  val result : unit
end

val go : prog -> meth -> unit
