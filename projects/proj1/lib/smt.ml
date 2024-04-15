open Base
open Z3
open Z3.Expr
open Z3.Sort
open Z3.Arithmetic

(** Status of a formula *)
type status =
  | Valid  (** formula is valid *)
  | Invalid of string  (** formula is invalid, with a counter-example *)
  | Unknown  (** formula status cannot be determined *)

(** Initialize z3 context *)
let ctx = mk_context [ ("model", "true"); ("proof", "false") ]

type env = (string, expr) List.Assoc.t
(** Map each variable to its Z3 expression *)

(** Int sort *)
let int_sort : sort = Integer.mk_sort ctx

(** Given a codomain sort, return an array sort that maps into the codomain sort *)
let arr_sort (codomain : sort) : sort = Z3Array.mk_sort ctx int_sort codomain

(** Convert a difny type to a Z3 sort *)
let rec sort_of_ty (t : Lang.ty) =
  match t with TInt -> int_sort | TArr t' -> arr_sort (sort_of_ty t')

(** Convert an [aexp] to a Z3 expression *)
let rec aexp (env : env) (e : Lang.aexp) : expr =
  let open Lang in
  match e with
  | Var x ->
      List.Assoc.find env x ~equal:String.equal
      |> Option.value_exn
           ~error:
             (Error.of_string
                Fmt.(str "Variable %s not found in environment" x))
  | Int n -> Integer.mk_numeral_i ctx n
  | Aop (o, e1, e2) ->
      let mk e1 e2 =
        match o with
        | Add -> Arithmetic.mk_add ctx [ e1; e2 ]
        | Sub -> Arithmetic.mk_sub ctx [ e1; e2 ]
        | Mul -> Arithmetic.mk_mul ctx [ e1; e2 ]
        | Div -> Arithmetic.mk_div ctx e1 e2
        | Mod -> Integer.mk_mod ctx e1 e2
      in
      mk (aexp env e1) (aexp env e2)
  | Select { arr; idx } -> Todo.at_level 2 ~msg:"Smt.aexp: Select"
  | Store { arr; idx; value } -> Todo.at_level 2 ~msg:"Smt.aexp: Store"

(** Convert a [formula] to a Z3 expression *)
let rec formula (env : env) (f : Lang.formula) : expr =
  let open Lang in
  match f with
  | FBool b -> if b then Boolean.mk_true ctx else Boolean.mk_false ctx
  | FConn (conn, f1, f2) ->
      let mk e1 e2 =
        match conn with
        | And -> Boolean.mk_and ctx [ e1; e2 ]
        | Or -> Boolean.mk_or ctx [ e1; e2 ]
        | Imply -> Boolean.mk_implies ctx e1 e2
        | Iff -> Boolean.mk_iff ctx e1 e2
      in
      mk (formula env f1) (formula env f2)
  | FNot f -> Boolean.mk_not ctx (formula env f)
  | FComp (o, e1, e2) ->
      let mk e1 e2 =
        match o with
        | Eq -> Boolean.mk_eq ctx e1 e2
        | Neq -> Boolean.mk_not ctx (Boolean.mk_eq ctx e1 e2)
        | Lt -> Arithmetic.mk_lt ctx e1 e2
        | Leq -> Arithmetic.mk_le ctx e1 e2
        | Gt -> Arithmetic.mk_gt ctx e1 e2
        | Geq -> Arithmetic.mk_ge ctx e1 e2
      in
      mk (aexp env e1) (aexp env e2)
  | FQ (q, x, f) ->
      let x_const = Arithmetic.Integer.mk_const_s ctx x in
      let is_forall = match q with Forall -> true | Exists -> false in
      Quantifier.mk_quantifier_const ctx is_forall [ x_const ]
        (formula ((x, x_const) :: env) f)
        None [] [] None None
      |> Quantifier.expr_of_quantifier

(** Convert a (variable, type) pair to a (variable, Z3 expr) pair where the Z3 expression 
  is a constant symbol of the appropriate sort *)
let convert ((x, t) : string * Lang.ty) : string * expr =
  let x_const = mk_const_s ctx x (sort_of_ty t) in
  (x, x_const)

(** Determine the validity status of a verification condition formula *)
let check_validity (gamma : Lang.gamma) (f : Lang.formula) : status =
  (* create solver instance *)
  let solver = Solver.mk_solver ctx None in
  (* TODO: translate the verification condition into a Z3 constraint *)
  let c =
    Todo.at_level 1 ~msg:"Smt.check_validity: c"
      ~dummy:(formula [] (FBool true))
  in
  Logs.debug (fun m ->
      m "Checking satisfiability of formula:\n%!%s"
        (SMT.benchmark_to_smtstring ctx
           (* comment *)
           "smtlib2 benchmark generated from difny verification condition"
           (* logic *)
           "" (* status *) "unknown" (* attributes *) "" (* assumptions *)
           [] (* formula *)
           c));
  (* invoke the solver to check constraint [c] *)
  let result = Solver.check solver [ c ] in
  Logs.debug (fun m -> m "Solver result: %s" (Solver.string_of_status result));
  (* call this function to obtain the counter-example string *)
  let model_str () =
    (* [x |> f |> g] means [g (f x)] in OCaml *)
    solver |> Solver.get_model
    |> Option.value_exn ~error:(Error.of_string "Solver returned no model")
    |> Model.to_string
  in
  Todo.at_level 1 ~msg:"Smt.check_validity: validity status" ~dummy:Unknown
