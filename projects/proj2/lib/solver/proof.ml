open Base

type t =
  | Fact of Clause.t  (** a known fact *)
  | Resolve of { left : t; on : Lit.t; right : t }

module Sequential = struct
  type step = Lit.t * Clause.t
  type t = { start : Clause.t; steps : step list }

  let pp_step ppf (l, c) = Fmt.pf ppf "@[@@[%a] %a@]" Lit.pp l Clause.pp c

  let pp ppf { start; steps } =
    let open Fmt in
    pf ppf "@[<v>%a@ %a@]" Clause.pp start (list pp_step) steps
end

let seq_of_t =
  let rec go acc = function
    | Fact start -> Some Sequential.{ start; steps = acc }
    | Resolve { left; on; right = Fact c } -> go ((on, c) :: acc) left
    | _ -> None
  in
  go []

let t_of_seq ({ start; steps } : Sequential.t) =
  List.fold_left steps ~init:(Fact start) ~f:(fun acc (on, c) ->
      Resolve { left = acc; on; right = Fact c })

let rec pp_verbose ppf = function
  | Fact c -> Clause.pp ppf c
  | Resolve { left; on; right } ->
      let open Fmt in
      pf ppf "resolve {@   @[<v>%a@]@ } @@[%a] {@   @[<v>%a@]@ }" pp_verbose
        left Lit.pp on pp_verbose right

let rec pp ppf p =
  match seq_of_t p with
  | Some seq -> Sequential.pp ppf seq
  | None -> (
      match p with
      | Fact c -> Clause.pp ppf c
      | Resolve { left; on; right } ->
          let open Fmt in
          pf ppf "resolve {@   @[<v>%a@]@ } @@[%a] {@   @[<v>%a@]@ }" pp left
            Lit.pp on pp right)

let replay (proof : t) : Clause.t =
  let rec go (facts : Set.M(Clause).t) = function
    | Fact c -> c
    | Resolve { left; on; right } ->
        let c1 = go facts left in
        let c2 = go facts right in
        Clause.resolve_exn c1 on c2
  in
  go (Set.empty (module Clause)) proof

let fact c = Fact c
let resolve ~left ~on ~right = Resolve { left; on; right }

let validate (assumptions : Set.M(Clause).t) (proof : t) =
  let rec replay facts = function
    | Fact c ->
        if Set.mem facts c then c
        else (
          Logs.err (fun m ->
              m "Claim %a isn't among the known facts" Clause.pp c);
          failwith "validate")
    | Resolve { left; on; right } ->
        let c1 = replay facts left in
        let c2 = replay facts right in
        Clause.resolve_exn c1 on c2
  in
  replay assumptions proof

let is_refutation (assumptions : Set.M(Clause).t) (p : t) : bool =
  let c = validate assumptions p in
  Set.is_empty c

let rec facts = function
  | Fact c -> Set.singleton (module Clause) c
  | Resolve { left; right; _ } -> Set.union (facts left) (facts right)
