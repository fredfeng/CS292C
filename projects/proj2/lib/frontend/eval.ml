open Base

type u = bool option [@@deriving equal]

let pp_u : u Fmt.t =
  Fmt.using
    (function None -> "??" | Some true -> "⊤" | Some false -> "⊥")
    Fmt.string

type t = bool Map.M(Var).t [@@deriving compare, equal]

let pp : t Fmt.t =
  let open Fmt in
  using
    (Map.filter_keys ~f:(fun x -> not (Var.equal x Var.dummy)))
    (Utils.pp_map ~sep:sp
       (`Pair
         (fun ppf (x, v) ->
           match v with
           | true -> pf ppf "%a" Var.pp x
           | false -> pf ppf "-%a" Var.pp x)))

let empty : t = Map.empty (module Var)
let set (nu : t) x v : t = Map.set nu ~key:x ~data:v

let of_lits (ls : Lit.t list) : t =
  let nu = empty in
  List.fold ls ~init:nu ~f:(fun nu l -> set nu (Lit.var l) (Lit.is_pos l))

let is_assigned (nu : t) (x : Var.t) = Map.mem nu x
let var (nu : t) (x : Var.t) : u = Map.find nu x

let lit nu (l : Lit.t) : u =
  if Lit.is_pos l then var nu (Lit.var l)
  else Option.map ~f:not (var nu (Lit.var l))

let clause nu (c : Clause.t) =
  (* a disjunction of literals is true if there exists a true literal *)
  Set.exists c ~f:(fun l -> lit nu l |> Option.value ~default:false)

let formula nu (f : Formula.t) =
  (* a conjunction of clauses is true if all clauses are true *)
  List.for_all f ~f:(clause nu)
