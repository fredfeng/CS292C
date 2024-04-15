open Base
open Lang

(** A value is either an int or an array *)
type value = VInt of int | VArr of arr

and arr = value Iarray.List.t * ty

let rec init (t : ty) : value =
  match t with TInt -> VInt 0 | TArr t -> VArr ([], t)

let rec random_of_ty = function
  | TInt -> VInt (Random.int 100)
  | TArr t ->
      let n = Random.int 100 in
      let a = ref Iarray.List.empty in
      for i = 0 to n do
        a := Iarray.List.store !a i (random_of_ty t)
      done;
      VArr (!a, t)

let arr_select ((a, _) : arr) (i : int) : value =
  Iarray.List.select a i
  |> Option.value_exn ~error:(Error.of_string Fmt.(str "out of bounds: %d" i))

let arr_store ((a, t) : arr) (i : int) (v : value) : arr =
  (Iarray.List.store a i v, t)

exception DifnyRuntimeError

type heap =
  | Heap of (string, value) List.Assoc.t  (** A heap maps variables to values *)

let heap_access (Heap h : heap) (x : string) : value =
  match List.Assoc.find h x ~equal:String.equal with
  | Some v -> v
  | None ->
      Logs.err (fun m -> m "Unbound variable %s" x);
      raise DifnyRuntimeError

let heap_mem (Heap h : heap) (x : string) : bool =
  List.Assoc.mem h x ~equal:String.equal

let heap_access_opt (Heap h : heap) (x : string) : value option =
  List.Assoc.find h x ~equal:String.equal

let heap_write (Heap h : heap) (x : string) (v : value) : heap =
  Heap ((x, v) :: h)

module Pretty = struct
  include Pretty
  open Fmt

  let rec value : value t =
   fun ppf -> function
    | VInt n -> int ppf n
    | VArr a -> Iarray.List.pp value ppf (fst a)

  let heap (gamma : gamma) : heap t =
   fun ppf h ->
    (vbox
    @@ iter_bindings
         (fun f -> List.iter ~f:(fun (x, _) -> f x (heap_access_opt h x)))
         (hbox @@ pair ~sep:(any " |-> ") string (option ~none:(any "*") value))
    )
      ppf gamma
end

module Eval (S : sig
  val prog : Lang.prog
  val meth : Lang.meth
end) =
struct
  let rec eval_aexp (h : heap) (e : aexp) : value =
    (* use OCaml's built-in integer operators to interpret  aop *)
    let eval_aop = function
      | Add -> ( + )
      | Sub -> ( - )
      | Mul -> ( * )
      | Div -> ( / )
      | Mod -> ( % )
    in
    match e with
    | Int n -> VInt n
    | Var x -> heap_access h x
    | Select { arr; idx } -> (
        match (eval_aexp h arr, eval_aexp h idx) with
        | VArr a, VInt i -> arr_select a i
        | v1, v2 ->
            Logs.err (fun m ->
                m "eval_aexp: select(%a, %a)" Pretty.value v1 Pretty.value v2);
            raise DifnyRuntimeError)
    | Store { arr; idx; value } -> (
        match (eval_aexp h arr, eval_aexp h idx, eval_aexp h value) with
        | VArr a, VInt i, v -> VArr (arr_store a i v)
        | v1, v2, v3 ->
            Logs.err (fun m ->
                m "eval_aexp: store(%a, %a, %a)" Pretty.value v1 Pretty.value v2
                  Pretty.value v3);
            raise DifnyRuntimeError)
    | Aop (o, e1, e2) -> (
        match (eval_aexp h e1, eval_aexp h e2) with
        | VInt n1, VInt n2 -> VInt (eval_aop o n1 n2)
        | v1, v2 ->
            Logs.err (fun m ->
                m "eval_aexp: %a %a %a" Pretty.value v1 Pretty.aop o
                  Pretty.value v2);
            raise DifnyRuntimeError)

  let rec eval_bexp (h : heap) (b : bexp) : bool =
    (* use OCaml's built-in integer comparisons to interpret  comp *)
    let eval_comp = function
      | Eq -> ( = )
      | Neq -> ( <> )
      | Lt -> ( < )
      | Gt -> ( > )
      | Leq -> ( <= )
      | Geq -> ( >= )
    in
    match b with
    | Bool b ->
        (* a constant evaluates to itself  *)
        b
    | Comp (o, e1, e2) -> (
        (* evaluate each operand to an integer value, then compare *)
        match (eval_aexp h e1, eval_aexp h e2) with
        | VInt n1, VInt n2 -> eval_comp o n1 n2
        | v1, v2 ->
            Logs.err (fun m ->
                m "eval_bexp: %a %a %a" Pretty.value v1 Pretty.comp o
                  Pretty.value v2);
            raise DifnyRuntimeError)
    | Not b1 ->
        (* use OCaml's built-in [not] operator *)
        not (eval_bexp h b1)
    | And (b1, b2) -> eval_bexp h b1 && eval_bexp h b2
    | Or (b1, b2) -> eval_bexp h b1 || eval_bexp h b2

  let rec eval_cmd (h : heap) (c : stmt) : heap =
    Logs.debug (fun m -> m "eval_cmd: %a" Pretty.stmt c);
    Logs.debug (fun m -> m "heap:\n%!%a" (Pretty.heap S.meth.locals) h);
    match c with
    | Assign { lhs; rhs } ->
        if not @@ heap_mem h lhs then (
          Logs.err (fun m -> m "Unbound variable %s" lhs);
          raise DifnyRuntimeError);
        (* evaluate rhs to a value *)
        let rhs_v = eval_aexp h rhs in
        heap_write h lhs rhs_v
    | If { cond; thn; els } ->
        if eval_bexp h cond then eval_block h thn else eval_block h els
    | While { cond; body; _ } -> eval_while h cond body
    | Assume _ | Assert _ -> h
    | Havoc x ->
        let rhs = random_of_ty (Lang.Utils.ty_exn S.meth.locals ~of_:x) in
        heap_write h x rhs
    | Print e ->
        let v = eval_aexp h e in
        Fmt.pr "%a\n%!" Pretty.value v;
        h
    | Call { lhs; callee; args } ->
        let vs = List.map ~f:(eval_aexp h) args in
        let callee =
          List.find S.prog ~f:(fun m -> String.equal m.id callee)
          |> Option.value_exn
               ~error:(Error.of_string Fmt.(str "unknown method: %s" callee))
        in
        (* map each parameter to arg value *)
        let h' =
          List.fold2_exn callee.params vs ~init:h ~f:(fun h (x, _) v ->
              heap_write h x v)
        in
        let h'' = eval_block h' callee.body in
        let rhs = eval_aexp h'' callee.ret in
        heap_write h lhs rhs

  and eval_while (h : heap) (cond : bexp) (body : block) : heap =
    Logs.debug (fun m ->
        m "eval_while: %a : %B" Pretty.bexp cond (eval_bexp h cond));
    if eval_bexp h cond then
      (* [cond] evaluates to [true], so we need to run the body once
          to obtain a new heap, then run the loop again *)
      eval_while (eval_block h body) cond body
    else (* [cond] evaluates to [false], so the loop is done *)
      h

  and eval_block (h : heap) : block -> heap = List.fold_left ~f:eval_cmd ~init:h
end

let eval_meth_with (p : prog) (h : heap) (meth : meth) : heap =
  let module E = Eval (struct
    let prog = p
    let meth = meth
  end) in
  E.eval_block h meth.body

let eval_meth (prog : prog) (meth : meth) =
  let final =
    eval_meth_with prog
      (Heap (List.map meth.locals ~f:(fun (x, t) -> (x, init t))))
      meth
  in
  Logs.app (fun m -> m ">>> Final heap:\n%!%a" (Pretty.heap meth.locals) final)
