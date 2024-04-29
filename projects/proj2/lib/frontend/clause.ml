open Base

type t = Set.M(Lit).t [@@deriving compare, equal, hash, sexp]

let pp : t Fmt.t =
 fun ppf ls ->
  if Set.is_empty ls then Fmt.string ppf "ε"
  else Fmt.pf ppf "@[<h>%a@]" (Utils.pp_set ~sep:Fmt.comma Lit.pp) ls

let vars c : Set.M(Var).t = Set.map (module Var) c ~f:Lit.var

let of_int_list (ns : int list) : t =
  ns |> List.map ~f:Lit.of_int |> Set.of_list (module Lit)

let contains (c : t) (l : Lit.t) : bool = Set.mem c l

let resolve (c1 : t) (l : Lit.t) (c2 : t) : t option =
  if Set.mem c1 l && Set.mem c2 (Lit.negate l) then
    Some (Set.union (Set.remove c1 l) (Set.remove c2 (Lit.negate l)))
  else None

let resolve_exn (c1 : t) (l : Lit.t) (c2 : t) : t =
  Utils.value_exn (resolve c1 l c2) ~error:(fun () ->
      Logs.err (fun m ->
          m "resolution failed: resolve %a (%a) %a" pp c1 Lit.pp l pp c2);
      failwith "resolve_exn")

let empty = Set.empty (module Lit)

include (val Comparator.make ~compare ~sexp_of_t)
