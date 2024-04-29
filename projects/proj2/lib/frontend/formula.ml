open Base

type t = Clause.t list [@@deriving compare, equal]

let pp : t Fmt.t = Fmt.(vbox @@ list ~sep:(any "; " ++ cut) Clause.pp)

let vars (f : t) : Set.M(Var).t =
  f
  |> List.fold
       ~init:(Set.empty (module Var))
       ~f:(fun acc c -> Set.union acc (Clause.vars c))

let of_ints (nss : int list list) : t = nss |> List.map ~f:Clause.of_int_list
