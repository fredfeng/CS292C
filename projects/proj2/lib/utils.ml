open Base

let partition4_map
    ~(f : 'a -> [ `P1 of 'b | `P2 of 'c | `P3 of 'd | `P4 of 'e ])
    (xs : 'a list) : 'b list * 'c list * 'd list * 'e list =
  let rec go xs (fst, snd, thd, forth) =
    match xs with
    (* | [] -> (List.rev fst, List.rev snd, List.rev thd, List.rev forth) *)
    | [] -> (fst, snd, thd, forth)
    | x :: xs' -> (
        match f x with
        | `P1 y -> go xs' (y :: fst, snd, thd, forth)
        | `P2 y -> go xs' (fst, y :: snd, thd, forth)
        | `P3 y -> go xs' (fst, snd, y :: thd, forth)
        | `P4 y -> go xs' (fst, snd, thd, y :: forth))
  in
  go xs ([], [], [], [])

let pp_map
    (pp_pair :
      [ `Pair of ('a * 'b) Fmt.t | `Arrow of 'a Fmt.t * unit Fmt.t * 'b Fmt.t ])
    ?(sep = Fmt.comma) ppf m =
  let pp_pair =
    match pp_pair with
    | `Pair pp -> pp
    | `Arrow (pp_key, arrow, pp_data) ->
        Fmt.(box @@ pair ~sep:arrow pp_key pp_data)
  in
  let uncurry f (a, b) = f a b in
  Fmt.(iter_bindings ~sep (fun f -> List.iter ~f:(uncurry f)) pp_pair)
    ppf (Map.to_alist m)

let pp_set ?(omit_after = None) ?sep pp_elt ppf s =
  let l = Set.to_list s in
  match omit_after with
  | Some n when List.length l > n ->
      let l' = List.take l n in
      Fmt.pf ppf "%a ..." Fmt.(list ?sep pp_elt) l'
  | _ -> Fmt.(list ?sep pp_elt) ppf l

let fold_until ~f ~init ~finish (xs : 'a list) =
  let rec go acc xs =
    match xs with
    | [] -> finish acc
    | x :: xs' -> (
        match f acc x xs' with
        | `Continue acc' -> go acc' xs'
        | `Stop acc' -> finish acc')
  in
  go init xs

let rec iter_with_tail ~f = function
  | [] -> ()
  | x :: xs ->
      f x xs;
      iter_with_tail ~f xs

let value_exn ~error = function Some x -> x | None -> error ()

let rec remove_first ~(f : 'a -> bool) = function
  | [] -> None
  | x :: xs -> (
      if f x then Some (x, xs)
      else
        match remove_first ~f xs with
        | None -> None
        | Some (y, ys) -> Some (y, x :: ys))
