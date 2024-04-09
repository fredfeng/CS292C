(* enum types in OCaml can not only contain data, but also be recursive *)

(* a singly-linked list is
   - either empty (a null ptr), 
   - or has a head element and a tail which points to another singly-linked list 
  We can encode this using OCaml's type *)
type list = 
  | Nil (* empty *) 
  | Cons of int * list (* head and tail *)
;;


(* How to make a list? by calling either the [Nil] or the [Cons] constructor: *)
(* we can always make an empty list *)
Nil;; 

(* if we're given a list, we can always make another list whose head is an int and whose tail is the given list *)
Cons (1, Nil);;

Cons (5, Cons (4, Cons (3, Nil)));;


(* recursive functions need to have the "rec" keyword *)
let rec length (l: list) : int = 
  match l with
  | Nil -> 0
  | Cons (x, t) -> 1 + length t
;;

(* Review of recursion:
   1. Iterative recursion: the recursive function f will have an accumulator argument.
    As you traverse the data structure, the accumulator will be updated at each step.
    when recursion reaches the base case, the accumulator is returned
    
   2. Induction/divide-and-conquer: the recursive function f will NOT have any accumulator.
    Instead, we call f on a "smaller problem" -- a part of the data structure that has the same "shape".
    We call f on the smaller problems, and assume the solutions to the sub-problems are correct by induction.
    Then we combine the solutions to the sub-problems into the solution to the original problem.
   *)


type maybe = OhNo | OhYeah of int
;;

(* max using iterative recursion *)
let max (l: list) : maybe = 
  let rec iter (l: list) (acc: int) : int =
    match l with
    | Nil -> acc
    | Cons (x, t) -> iter t (if x > acc then x else acc)
  in
  match l with
  | Nil -> OhNo
  | Cons (x, t) -> OhYeah (iter t x)
;;


(* max using induction *)
let rec max_ind (l: list) : maybe =
  match l with
  | Nil -> OhNo
  | Cons (x, t) -> 
    OhYeah (match max_ind t with
    | OhNo -> x
    | OhYeah y -> (if x > y then x else y))


(* question: what if we want to compute the length of a list of booleans? *)

  (* Cons (true, Cons (false, Nil));; *) (* this fails to type check *)


(* problem: we defined list to only contain integer elements *)
(* non-solution: define a bool_list type and reimplement length for this type *)
type bool_list = 
  | NilBool
  | ConsBool of bool * bool_list
;;
let rec length_bool_list (l: bool_list) : int = 
  match l with
  | NilBool -> 0
  | ConsBool (x, t) -> 1 + length_bool_list t
;;

(* This is bad because we duplicated code for no reason: length doesn't need to know 
   the type of elements in a list, only how long the list is *)

  (* In Java/C++/Rust/other popular languages, this feature is called "generics".
     In functional programming, this is called "polymorphism" *)

(* solution: use polymorphism *)
type 'a list = 
  | Nil
  | Cons of 'a * 'a list
;;

(* 'a is a generic "type variable" that can be instantiated with other types
   for example, we can write down [int list] [bool list] [string list] [int list list] [(int * string) list] and so on *)

Cons (1, Cons (2, Nil));; (* works *)
Cons (true, Cons (false, Nil));; (* works *)
Cons ("hello", Cons ("world", Nil));; (* works *)
Cons (Cons (1, Nil), Cons (Cons (2, Cons (3, Nil)), Nil));; (* works *)
Cons (1, Cons (true, Nil));; (* does NOT work -- heterogenous lists are not allowed *)

(* we can also write a single polymorphic length function that works on any list *)
let rec length (l: 'a list) : int = 
  match l with
  | Nil -> 0
  | Cons (x, t) -> 1 + length t
;;

(* as you can see, OCaml's enum type is extremely powerful *)

(* so power that you easily use it to represent programs! *)

(* for example, here's the grammar that defines IMP expressions:
  E = Z | X | E + E | E * E 
  we can represent this grammar in OCaml *)
type expr = 
  | EInt of int
  | EVar of string
  | EAdd of expr * expr
  | EMul of expr * expr
;;

(* this is called the "abstract syntax tree" representation of IMP expressions,
   to contrast with concrete syntax.
   
   Concrete syntax = a string you and me as developers write down in a text editor 
   Abstract syntax = a tree representation of the same program that are easier to manipulate by
    compilers, program verifiers, and so on 
*)





