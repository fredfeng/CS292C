open Base

exception Unassigned

module Delta = struct
  type t = int Map.M(Var).t

  let empty = Map.empty (module Var)

  let pp ppf delta =
    Utils.pp_map (`Arrow (Var.pp, Fmt.(any " @@ "), Int.pp)) ppf delta
end

module Trail = struct
  type t = { decision : Lit.t; implied : Lit.t list }

  let pp ppf { decision; implied } =
    Fmt.(hbox (pair ~sep:(any " | ") Lit.pp (list ~sep:sp Lit.pp)))
      ppf (decision, implied)
end

module Trails = struct
  type t = Trail.t Map.M(Int).t

  let pp : t Fmt.t =
    Fmt.(vbox (Utils.pp_map (`Arrow (Int.pp, Fmt.(any " : "), Trail.pp))))

  let empty = Map.empty (module Int)
end

module Imp = struct
  type t = Clause.t Map.M(Lit).t

  let pp ppf t =
    Utils.pp_map (`Pair Fmt.(pair ~sep:(any " ==> ") Lit.pp Clause.pp)) ppf t

  let empty : t = Map.empty (module Lit)
end

type t = {
  nu : Eval.t;
  delta : int Map.M(Var).t; [@opaque]
      (** Map variables to their decision levels *)
  trails : Trails.t;
  imp : Imp.t;
}
[@@deriving show]
(** Main variable assignment data structure *)

(** Create an empty assignment for n variables *)
let empty : t =
  {
    nu = Eval.empty;
    delta = Delta.empty;
    trails = Trails.empty;
    imp = Imp.empty;
  }

let is_assigned (a : t) (x : Var.t) : bool =
  let b1 = Eval.is_assigned a.nu x in
  let b2 = Option.is_some (Map.find a.delta x) in
  (* invariant: [x] is in the assignment map iff it's in the delta map *)
  assert (Bool.(b1 = b2));
  b1

let antecedent (a : t) (l : Lit.t) : Clause.t option = Map.find a.imp l

(** Assign an implied literal to true at leval i *)
let assign { nu; delta; trails; imp } ~level:i ?antecedent lit : t =
  let is_decision = Option.is_none antecedent in
  let v = Lit.var lit in
  {
    nu = Eval.set nu v Lit.(is_pos lit);
    delta = Map.set delta ~key:v ~data:i;
    imp =
      (match antecedent with
      | None -> imp
      | Some c -> Map.add_exn imp ~key:lit ~data:c);
    trails =
      Map.update trails i ~f:(function
        | None ->
            if is_decision then { Trail.decision = lit; implied = [] }
            else (
              Logs.err (fun m -> m "No level %d in trails" i);
              failwith "assign")
        | Some trail ->
            if is_decision then (
              Logs.err (fun m -> m "Trails %d already in trails" i);
              failwith "assign")
            else { trail with implied = lit :: trail.implied });
  }

let assign_decision a level lit = assign a ~level lit
let assign_implied a level antecedent lit = assign a ~level ~antecedent lit
let level a lit = Map.find a.delta (Lit.var lit)

let level_exn a lit =
  Map.find a.delta (Lit.var lit)
  |> Utils.value_exn ~error:(fun () -> raise Unassigned)

let trail_exn a i =
  Map.find a.trails i |> Utils.value_exn ~error:(fun () -> raise Unassigned)

let invariant n ~level:lvl { nu; delta; trails; _ } =
  let level_mapped = ref (Set.empty (module Var)) in
  Map.iteri trails ~f:(fun ~key ~data:trail ->
      assert (key >= 0);
      assert (key <= lvl);
      level_mapped :=
        Set.union !level_mapped
          (Set.of_list
             (module Var)
             (List.map (trail.decision :: trail.implied) ~f:Lit.var)));
  (* (Set.of_list
     (module Var)
     (List.map ~f:Lit.var (trail.decision :: trail.implied)))); *)
  for i = 1 to n do
    let v = Var.of_int i in
    let b1 = Eval.is_assigned nu v in
    let b2 = Option.is_some (Map.find delta v) in
    let b3 = Set.mem !level_mapped v in
    if Bool.(b3 <> b1) then (
      Logs.err (fun m ->
          Logs.err (fun m -> m " %a" Eval.pp nu);
          Logs.err (fun m -> m "Delta: %a" Delta.pp delta);
          Logs.err (fun m -> m "Trails: %a" Trails.pp trails);
          m "Variables in level map: %a"
            (Utils.pp_set Var.pp ~omit_after:None)
            !level_mapped);
      Logs.err (fun m ->
          m "Variable %a in level map? %b\tassigned? %b" Var.pp v b3 b1);
      assert false);
    assert (Bool.(b1 = b2));
    Option.iter (Map.find delta v) ~f:(fun l ->
        if not (l >= 0 && l <= lvl) then (
          Logs.err (fun m ->
              m "Variable %a has invalid decision level %d" Var.pp v l);
          assert false))
  done

let pp_clause_with ~f pp_with ppf (c : Clause.t) : unit =
  let with_ = c |> Set.to_list |> List.map ~f:(fun l -> (l, f l)) in
  Fmt.pf ppf "Conflict: %a"
    Fmt.(list ~sep:sp (pair ~sep:(any "/") Lit.pp pp_with))
    with_

let pp_clause_with_level (a : t) : Clause.t Fmt.t =
  pp_clause_with ~f:(fun l -> level a l) Fmt.(option int ~none:(any "??"))

let pp_clause_with_value (a : t) : Clause.t Fmt.t =
  pp_clause_with ~f:(fun l -> Eval.lit a.nu l) Eval.pp_u
