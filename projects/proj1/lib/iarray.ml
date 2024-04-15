open Base

(** Signature for McCarthy's immutable arrays that supports
  three operations: [empty], [select] and [store].
  The immutability means that [store] will not modify the original array,
  but instead return a new array.
  
  The three operations are completely characterized by the following axioms:
  
  1. Reading from the empty array returns nothing:
  
    [select empty i] = [None] for all [i]
  
  2. If you store a value at index [i], then reading the [i]-th element
    of the resulting array should return the newly stored value:
  
    [select (store a i v) i] = [Some v] for all [i]
  
  3. If you store a value at index [i], then reading the [j]-th element
    of the resulting array should return the same value as reading the
    [j]-th element of the original array, assuming [j] isn't [i]: 
  
    [select (store a i v) j] = [select a j]  for all [j] such that [j <> i] *)
module type IARRAY = sig
  type 'a t
  (** Type for immutable arrays *)

  val empty : 'a t
  (** Create an empty array *)

  val select : 'a t -> int -> 'a option
  (** [select a i] reads the [i]-th element of array [a],
      and returns an option. If the index is out of bounds,
      it returns [None]. *)

  val store : 'a t -> int -> 'a -> 'a t
  (** [store a i v] returns a new array whose content is the
      same as [a], but the [i]-th element is replaced by [v].
      The original array [a] is not modified. *)

  val pp : 'a Fmt.t -> 'a t Fmt.t
  (** Pretty-printer for arrays *)
end

(** Immutable array implementation using association lists *)
module List : IARRAY with type 'a t = (int, 'a) List.Assoc.t = struct
  (* = struct *)
  type 'a t = (int, 'a) List.Assoc.t

  let equal = Int.equal
  let empty = []
  let select a i = List.Assoc.find a i ~equal
  let store a i v = List.Assoc.add (List.Assoc.remove a i ~equal) i v ~equal

  let pp pp_v ppf a =
    let open Fmt in
    brackets
      (list ~sep:comma (pair ~sep:(any ":") int pp_v))
      ppf
      (List.sort a ~compare:(fun (i, _) (j, _) -> Int.compare i j))
end
