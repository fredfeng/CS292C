open Lang
open Fmt

let aop : aop t =
  using
    (function Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%")
    string

let rec aexp : aexp t =
  let is_complex = function Aop _ -> true | _ -> false in
  (* parenthesized *)
  let p ppf e = if is_complex e then parens aexp ppf e else aexp ppf e in
  fun ppf -> function
    | Int n -> int ppf n
    | Aop (op, e1, e2) -> pf ppf "@[%a %a %a@]" p e1 aop op p e2
    | Var x -> pf ppf "%s" x
    | Select { arr; idx } -> pf ppf "select(@[%a, %a@])" aexp arr aexp idx
    | Store { arr; idx; value } ->
        pf ppf "store(@[%a,@ %a,@ %a@])" aexp arr aexp idx aexp value

and path : path t =
 fun ppf { var; indices } ->
  pf ppf "@[<h>%a%a@]" string var (list (brackets aexp)) indices

let comp : comp t =
  using
    (function
      | Eq -> "=="
      | Neq -> "!="
      | Lt -> "<"
      | Leq -> "<="
      | Gt -> ">"
      | Geq -> ">=")
    string

let rec bexp : bexp t =
  let is_complex : bexp -> bool = function
    | And _ | Or _ -> true
    | _ -> false
  in
  let p ppf b = if is_complex b then parens bexp ppf b else bexp ppf b in
  fun ppf -> function
    | Bool b -> bool ppf b
    | Comp (op, e1, e2) -> pf ppf "@[%a %a %a@]" aexp e1 comp op aexp e2
    | Not b -> pf ppf "!%a" p b
    | And (b1, b2) -> pf ppf "@[%a && %a@]" p b1 p b2
    | Or (b1, b2) -> pf ppf "@[%a || %a@]" p b1 p b2

let quantifier : quantifier t =
  using (function Forall -> "forall" | Exists -> "exists") string

let connective : connective t =
  using
    (function And -> "&&" | Or -> "||" | Imply -> "==>" | Iff -> "<=>")
    string

let rec formula : formula t =
  let is_complex = function FQ _ | FConn _ -> true | _ -> false in
  let p ppf f = if is_complex f then parens formula ppf f else formula ppf f in
  fun ppf -> function
    | FBool b -> bool ppf b
    | FComp (o, e1, e2) -> pf ppf "@[%a %a@ %a@]" aexp e1 comp o aexp e2
    | FQ (q, x, f) -> pf ppf "@[<2>%a %s ::@ %a@]" quantifier q x formula f
    | FNot f -> pf ppf "!%a" (parens formula) f
    | FConn (op, f1, f2) -> pf ppf "%a %a@ %a" p f1 connective op p f2

let rec stmt : stmt t =
  let invariant ppf f = pf ppf "  @[<2>invariant %a@]" formula f in
  fun ppf -> function
    | Assign { lhs; rhs } -> pf ppf "%s := %a;" lhs aexp rhs
    | If { cond; thn; els } ->
        pf ppf "if %a %a else %a" bexp cond block thn block els
    | While { cond; inv = []; body } ->
        pf ppf "while (%a)@ %a" bexp cond block body
    | While { cond; inv; body } ->
        pf ppf "while (%a)@\n%a %a" bexp cond
          (vbox (list invariant))
          inv block body
    | Assume f -> pf ppf "assume %a;" formula f
    | Assert f -> pf ppf "assert %a;" formula f
    | Havoc x -> pf ppf "%s := *;" x
    | Print e -> pf ppf "print(@[%a@]);" aexp e
    | Call { lhs; callee; args } ->
        pf ppf "%s := %s(@[%a@]);" lhs callee (list ~sep:comma aexp) args

and block ppf coms = pf ppf "{@   @[<v>%a@]@ }" (list ~sep:cut stmt) coms

let rec ty : ty t =
 fun ppf -> function
  | TInt -> string ppf "int"
  | TArr t -> pf ppf "array<%a>" ty t

let meth : meth t =
  let param = pair ~sep:(any ": ") string ty in
  let local ppf (x, t) = pf ppf "var %s: %a;@ " x ty t in
  let pp_returns ppf (x, t) = pf ppf "returns (%s: %a)" x ty t in
  let pp_requires ppf f = pf ppf "requires %a@ " formula f in
  let pp_ensures ppf f = pf ppf "ensures %a@ " formula f in
  let pp_ret ppf e = pf ppf "return %a;" aexp e in
  fun ppf { id; params; returns; requires; ensures; locals; body; ret } ->
    pf ppf "method %s(%a) %a@\n  @[<v>%a%a@]@\n{@   @[<hv>%a%a@ %a@]@\n}@\n" id
      (* params *)
      (hvbox @@ list ~sep:comma param)
      params (* returns *)
      pp_returns returns
      (* requires *)
      (list ~sep:nop pp_requires)
      requires
      (* ensures *)
      (list ~sep:nop pp_ensures)
      ensures (* locals *)
      (list ~sep:nop local) locals (* body *)
      (list stmt) body (* return *)
      pp_ret ret

let prog : prog t = vbox @@ list ~sep:(cut ++ cut) meth

let rec gcom : gcom t =
 fun ppf -> function
  | Assume f -> pf ppf "assume %a;" formula f
  | Assert f -> pf ppf "assert %a;" formula f
  | Havoc x -> pf ppf "havoc %s;" x
  | Seq cs -> vbox (list gcom) ppf cs
  | Choose (c1, c2) ->
      pf ppf "choose {@\n   %a@ } || {@    %a@ }" gcom c1 gcom c2
