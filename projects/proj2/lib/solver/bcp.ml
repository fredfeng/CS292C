open Base

type status = Sat | Unsat | Unit of Lit.t | Unresolved

let status (nu : Eval.t) (c : Clause.t) : status =
  match
    List.partition3_map (Set.to_list c) ~f:(fun l ->
        match Eval.lit nu l with
        | Some false -> (* false *) `Fst l
        | None -> (* unassigned *) `Snd l
        | Some true -> (* true *) `Trd l)
  with
  | _, _, _ -> Todo.part 1 "Bcp.status"

type result = Unsat of Clause.t | Unknown | Sat

let run (level : int) (a : Assign.t) (cs : Clause.t list) : result * Assign.t =
  Todo.part 1 "Bcp.run"
