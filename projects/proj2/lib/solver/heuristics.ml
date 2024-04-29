open Base

type score = float
type t = score Hashtbl.M(Lit).t

let episodes = ref 0
let smooth_threshold = 100
let smooth_factor = 10.

let pp : t Fmt.t =
  Fmt.(
    using
      (fun h -> Hashtbl.to_alist h |> Map.of_alist_exn (module Lit))
      (hovbox
      @@ Utils.pp_map ~sep:comma (`Pair (pair ~sep:(any ": ") Lit.pp float))))

let empty () = Hashtbl.create (module Lit)

let init (f : Formula.t) (t : t) =
  List.iter f
    ~f:
      (Set.iter ~f:(fun l ->
           Hashtbl.update t l ~f:(function None -> 1. | Some w -> w +. 1.)))

let new_episode t =
  Int.incr episodes;
  if !episodes > smooth_threshold then
    Hashtbl.map_inplace t ~f:(fun score -> score /. smooth_factor)

let incr t l = Hashtbl.update t l ~f:(function None -> 1. | Some w -> w +. 1.)

let record_conflict (t : t) (c : Clause.t) =
  Set.iter c ~f:(fun l -> incr t l);
  new_episode t

let score t l = Hashtbl.find t l |> Option.value ~default:0.

let best_phase t v =
  let pos = Lit.make_pos v in
  let neg = Lit.make_neg v in
  if Float.compare (score t pos) (score t neg) > 0 then (pos, score t pos)
  else (neg, score t neg)

(** Randomly select an unassigned variable *)
let unassigned ~random (vars : Set.M(Var).t) (a : Assign.t) : Var.t option =
  let exception Found of Var.t in
  let num_vars = Set.length vars in
  let rand = if random then Random.int num_vars else 0 in
  try
    for i = 0 to num_vars - 1 do
      let j = ((rand + i) % num_vars) + 1 in
      let x = Var.of_int j in
      if not (Assign.is_assigned a x) then raise (Found x)
    done;
    None
  with Found x -> Some x

let next_unassigned = unassigned ~random:false

let random_unassigned vars a =
  Option.map
    (unassigned ~random:true vars a)
    ~f:(if Random.bool () then Lit.make_pos else Lit.make_neg)

let best_unassigned (vars : Set.M(Var).t) (a : Assign.t) (t : t) : Lit.t option
    =
  let unassigned =
    Set.filter vars ~f:(fun v -> not (Eval.is_assigned a.nu v))
  in
  let max = ref None in
  let max_score = ref Float.neg_infinity in
  Set.iter unassigned ~f:(fun v ->
      let l, s = best_phase t v in
      if Float.(s > !max_score) then (
        max := Some l;
        max_score := s));
  !max
