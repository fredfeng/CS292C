(** Proof scripts *)

open Base

module Lemma = struct
  type t = { goal : Clause.t; proof : Proof.t }

  let pp ppf { goal; proof } =
    let open Fmt in
    pf ppf "@[<v>Lemma: %a.@ Proof.@   %a@ Qed.@ @]" Clause.pp goal Proof.pp
      proof

  let make goal proof = { goal; proof }
end

type t = { lemmas : Lemma.t list; main : Proof.t }

let pp ppf { lemmas; main } =
  let open Fmt in
  pf ppf "@[<v>%a@ Theorem: %a.@ Proof. @   %a@ Qed.@]" (list ~sep:cut Lemma.pp)
    lemmas Clause.pp Clause.empty Proof.pp main

let make (lemmas : Lemma.t list) (main : Proof.t) : t = { lemmas; main }

let compactify (assumptions : Set.M(Clause).t) ({ lemmas; main } : t) =
  let lemma_map =
    lemmas
    |> List.map ~f:(fun Lemma.{ goal; proof } -> (goal, proof))
    |> Map.of_alist_reduce (module Clause) ~f:(fun p _ -> p)
  in
  let used = ref (Set.empty (module Clause)) in
  let rec fixpoint (cs : Set.M(Clause).t) =
    Logs.info (fun m ->
        m "Fixpointing with %a" Fmt.(vbox @@ list Clause.pp) (Set.to_list cs));
    match Set.choose cs with
    | Some c when not (Set.mem assumptions c) ->
        used := Set.add !used c;
        fixpoint
          Set.(
            remove
              (union cs (diff (Proof.facts (Map.find_exn lemma_map c)) !used))
              c)
    | Some c -> fixpoint (Set.remove cs c)
    | None -> ()
  in
  fixpoint (Set.singleton (module Clause) Clause.empty);
  let lemmas =
    lemmas |> List.filter ~f:(fun Lemma.{ goal; _ } -> goal |> Set.mem !used)
  in
  { lemmas; main }

let validate (assumptions : Set.M(Clause).t) ({ lemmas; main } : t) =
  let proved =
    List.fold_left lemmas ~init:assumptions ~f:(fun facts { goal; proof } ->
        let proved = Proof.validate facts proof in
        (* check that what is proven indeed implies the goal statement *)
        if Set.is_subset goal ~of_:proved then Set.add facts goal
        else (
          Logs.err (fun m ->
              m "Proof for lemma %a failed, and proved %a instead" Clause.pp
                goal Clause.pp proved);
          failwith "validate"))
  in
  Proof.validate proved main

let is_refutation (assumptions : Set.M(Clause).t) (script : t) =
  let proved = validate assumptions script in
  Set.is_empty proved
