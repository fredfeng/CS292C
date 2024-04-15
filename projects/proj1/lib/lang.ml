open Base

(** Arithmetic op *)
type aop = Add | Sub | Mul | Div | Mod

(** Arithmetic expression *)
type aexp =
  | Int of int  (** integer constant *)
  | Aop of aop * aexp * aexp  (** arithmetic op *)
  | Var of string  (** variable *)
  | Select of { arr : aexp; idx : aexp }  (** McCarthy's array read *)
  | Store of { arr : aexp; idx : aexp; value : aexp }
      (** McCarthy's array write *)

type path = { var : string; indices : aexp list }
(** Variable / array access path expression *)

let var_of_path (p : path) : string =
  match p.indices with
  | [] -> p.var
  | _ -> failwith Fmt.(str "var_of_path: %s is not a variable" p.var)

(** Comparison op *)
type comp = Eq | Neq | Lt | Leq | Gt | Geq

(** Boolean expression *)
type bexp =
  (* boolean constant *)
  | Bool of bool
  (* integer comparison *)
  | Comp of comp * aexp * aexp
  (* negation *)
  | Not of bexp
  (* conjunction *)
  | And of bexp * bexp
  (* disjunction *)
  | Or of bexp * bexp

(** Quantifier *)
type quantifier = Forall | Exists

(** Logical connective *)
type connective = And | Or | Imply | Iff

(** First-order logic formula *)
type formula =
  | FBool of bool  (** boolean constant *)
  | FComp of comp * aexp * aexp  (** integer comparison *)
  | FQ of quantifier * string * formula
      (** first-order quantification over an integer variable *)
  | FNot of formula  (** negation of a formula *)
  | FConn of connective * formula * formula  (** logical connective *)

(** Statement *)
type stmt =
  (* assignment, aka memory write *)
  | Assign of { lhs : string; rhs : aexp }
  (* conditional *)
  | If of { cond : bexp; thn : block; els : block }
  (* while-loop *)
  | While of { cond : bexp; inv : formula list; body : block }
  (* assume *)
  | Assume of formula
  (* assert *)
  | Assert of formula
  (* havoc *)
  | Havoc of string
  (* print *)
  | Print of aexp
  (* function call *)
  | Call of { lhs : string; callee : string; args : aexp list }

and block = stmt list
(** A block is a sequence of commands *)

(** Type *)
type ty = TInt  (** integer type *) | TArr of ty  (** array type *)

type gamma = (string * ty) list
(** gamma maps variables to their types *)

type meth = {
  id : string;  (** method name *)
  params : gamma;  (** method parameters *)
  returns : string * ty;  (** return identifier and type *)
  requires : formula list;  (** preconditions *)
  ensures : formula list;  (** postconditions *)
  locals : gamma;  (** local variables *)
  body : block;  (** method body *)
  ret : aexp;  (** return statement *)
}
(** Method *)

type prog = meth list
(** Program *)

(** Guarded command *)
type gcom =
  | Assume of formula
  | Assert of formula
  | Havoc of string
  | Seq of gcom list
  | Choose of gcom * gcom

module Utils = struct
  exception Unbound

  let ty (gamma : gamma) ~of_:(x : string) : ty option =
    List.Assoc.find gamma x ~equal:String.equal

  let ty_exn (gamma : gamma) ~of_:(x : string) : ty =
    match ty gamma ~of_:x with
    | Some t -> t
    | None ->
        Logs.err (fun m -> m "Unbound variable %s" x);
        raise Unbound
end

(** Helper functions to build Difny expressions and formulas *)
module Syntax = struct
  let ( ! ) x = Var x
  let i n = Int n
  let ( + ) e1 e2 = Aop (Add, e1, e2)
  let ( - ) e1 e2 = Aop (Sub, e1, e2)
  let ( * ) e1 e2 = Aop (Mul, e1, e2)
  let ( / ) e1 e2 = Aop (Div, e1, e2)
  let ( % ) e1 e2 = Aop (Mod, e1, e2)
  let select arr idx = Select { arr; idx }
  let store arr idx value = Store { arr; idx; value }

  module Bexp = struct
    let true_ = Bool true
    let false_ = Bool false
    let ( == ) e1 e2 = Comp (Eq, e1, e2)
    let ( != ) e1 e2 = Comp (Neq, e1, e2)
    let ( < ) e1 e2 = Comp (Lt, e1, e2)
    let ( <= ) e1 e2 = Comp (Leq, e1, e2)
    let ( > ) e1 e2 = Comp (Gt, e1, e2)
    let ( >= ) e1 e2 = Comp (Geq, e1, e2)
    let ( && ) b1 b2 : bexp = And (b1, b2)
    let ( || ) b1 b2 : bexp = Or (b1, b2)
    let not b = Not b
  end

  module Formula = struct
    let forall x f = FQ (Forall, x, f)
    let exists x f = FQ (Exists, x, f)
    let true_ = FBool true
    let false_ = FBool false
    let ( && ) f1 f2 = FConn (And, f1, f2)
    let ( || ) f1 f2 = FConn (Or, f1, f2)
    let ( ==> ) f1 f2 = FConn (Imply, f1, f2)
    let ( <=> ) f1 f2 = FConn (Iff, f1, f2)
    let not f = FNot f
    let ( == ) e1 e2 = FComp (Eq, e1, e2)
    let ( != ) e1 e2 = FComp (Neq, e1, e2)
    let ( < ) e1 e2 = FComp (Lt, e1, e2)
    let ( <= ) e1 e2 = FComp (Leq, e1, e2)
    let ( > ) e1 e2 = FComp (Gt, e1, e2)
    let ( >= ) e1 e2 = FComp (Geq, e1, e2)
  end

  module Stmt = struct
    let ( := ) lhs rhs = Assign { lhs; rhs }
    let havoc x : stmt = Havoc x
    let assume f : stmt = Assume f
    let assert_ f : stmt = Assert f
    let if_ cond thn els : stmt = If { cond; thn; els }
    let while_ ?(inv = []) cond body : stmt = While { cond; inv; body }
    let print e : stmt = Print e
    let call ~lhs callee args : stmt = Call { lhs; callee; args }
  end

  module GCom = struct
    let assume f : gcom = Assume f
    let assert_ f : gcom = Assert f
    let havoc x : gcom = Havoc x
    let seq cs : gcom = Seq cs
    let choose c1 c2 : gcom = Choose (c1, c2)
  end
end
