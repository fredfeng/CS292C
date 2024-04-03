(* to make booleans: boolean constants*)
true;;

false;;

(* to use booleans: if-then-else *)
if true then 1 else 3;;

(* two branches must have the same type *)
if true then 1>0 else 3;;

(* other uses of boolean can be implemented in terms of if-then-else *)
(* [b1 && b2] equivalent to [if b1 then b2 else false] *)

(* to make integers: int constants *)
1;;
0;;
-100;;

(* to use integers: arithmetic operations *)
1 + 2;;
3 > 4;;

(* to make a pair: use paren + comma *)
(1, 2);;
(* the two components need not have the same type *)
(1, "hello");;

(* to use a pair: use fst / snd *)
fst (1, 2);; (* evaluates to 1 *)
snd ("hello", false);; (* evaluates to false *)

(* bindings *)
let x = 1 in x + 1;; (* x is bound to 1, and is in scope only in [x+1] *)

x;; (* unbound *)

(* bindings are not mutation *)
let x = 1 in (let x = x+1 in x) + x;; (* evaluates to 3, because [let x = x+1 in x] evaluates to 2 *)

(* [let] can also be used to make/define functions *)
let add (x: int) (y: int) : int = x + y;;

(* or use [fun] *)
let add : int -> int -> int = fun x y -> x+y;;

(* function calls *)

add 3 4;; (* evaluates to 7 *)


(* an enum type is defined by listing out all cases, i.e. how to make it *)
type day_of_week = 
  Mon | Tue | Wed | Thu | Fri | Sat | Sun;;

(* to make a [day_of_week], simply call one of the "constructors" *)
let day = Mon;;

(* to use a [day_of_week], use pattern matching *)
let feeling (day: day_of_week) = 
  match day with
  | Mon -> print_endline "gloomy"
  | Tue -> print_endline "better"
  | Wed -> print_endline "hump day"
  | Thu -> print_endline "almost there"
  | Fri -> print_endline "yay"
  | Sat -> print_endline "happy"
  | Sun -> print_endline "dread"
;;

feeling Mon;; (* this will print "gloomy" and return nothing *)

(* OCaml's enum is much more powerful: each case can be packaged with some data *)
type maybe = OhNo | OhYeah of int;;

(* to make a maybe, either do *)
let m1 = OhNo;;

(* or *)
let m2 = OhYeah 3;;

(* example *)
let safe_div (x: int) (y: int) : maybe =
  if y = 0 then OhNo else OhYeah (x/y);;

(* to use a maybe, use pattern matching *)
let add1 (m: maybe) : maybe =
  match m with
  | OhNo -> OhNo
  | OhYeah x -> 
    (* if we just put (x+1) here, the program will not type-check *)
    (* this is because every branch must have the same type, just like if-then-else *)
    OhYeah (x+1) 
;;