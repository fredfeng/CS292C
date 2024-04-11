# CS292C Homework 2

**Due: 4/15/2019 11:59pm**


## Instructions

1. Compose your answers and code in a PDF file.
2. On the first page of the PDF file, include a table that contains a self-grade (0, 1, or 2) for each problem. See the [course syllabus](/README.md) for the self-grading rubric.
3. Submit your PDF file to Gradescope.


### Problem 1

Install OCaml by following the [these instructions](./install.md).

This may take more than 30 minutes depending on how beefy your computer is, so **do not wait until the last minute to install OCaml**.

Once you're done, enter `utop` and evaluate the following expression:
```ocaml
print_endline "I have installed OCaml!"
```

Include a screenshot of all of `utop`'s output thus far (including the welcome message) to your PDF file.

If you run into any issues, post in the `#tech-support` Slack channel.



---
It is highly recommended that you install OCaml locally before proceeding with the rest of the homework, rather than using an online interpreter.


### Problem 2

Implement a function `compress : ('a -> 'a -> bool) -> 'a list  -> 'a list` that will take a list and return a new list with all consecutive duplicate elements removed. For example:

```ocaml
# compress String.equal ["a";"a";"a";"a";"b";"c";"c";"a";"a";"d";"e";"e";"e";"e"];;
- : string list = ["a"; "b"; "c"; "a"; "d"; "e"]
```

Your function should use the first argument `'a -> 'a -> bool` to test for equality between two values of type `'a`. Do NOT use the polymorphic equality `=` unless you're comparing two integers.

When you're testing your implementation, the equality functions for `int`, `string`, and `bool` are already defined in the OCaml standard library as `Int.equal`, `String.equal`, and `Bool.equal`, respectively. You can use them directly in your tests. List equality is also defined in the standard library as `List.equal`.

In your PDF file, include the definition of your function, along with **three distinct, non-trivial test cases and their output** to show that your function works correctly.



### Problem 3

In class, you saw the `maybe` type:
    
```ocaml
type maybe = OhNo | OhYeah of int
```
which can be used to represent outcomes of computation that may either succeed with an integer, or fail with no result at all.

However, the `maybe` can only be used with computation returning integers. Luckily, OCaml provides a polymorphic version of `maybe` called `'a option`:

```ocaml
type 'a option = None | Some of 'a
```

For example, `maybe` is essentially the same thing as `int option`, but now you can have `string option`, `bool option`, or even `int int option`.

Implement the function `merge: 'a option list -> 'a list option` that takes a list of options, and if all of the options are `Some ...` for some `x`, then it returns `Some [ ... ]`, where `...` are the values contained in the options. Otherwise, it returns `None`.

For example, `merge [Some 1; Some 2; Some 3]` will evaluate to `Some [1; 2; 3]`, and `merge [Some 1; None; Some 3]` will evaluate to `None`.



In your PDF file, include the definition of your function, along with **three distinct, non-trivial test cases and their output** to show that your function works correctly.


> **Important OCaml note:** Indentations don't matter in OCaml. As a corollary, if you want to write a nested pattern match like
> ```ocaml
> (* BAD CODE *)
> match x with
> | Some y -> 
>     match
>     | Some z -> ...
>     | None -> ...
> | None -> (* !!! *)
> ```
> The OCaml compiler would not know that the `None` case in the last line (marked with `(* !!! *)`) is supposed to be part of the outer pattern match. Instead, it will think by default that the `None` belongs to the inner pattern match, which is not what you want, and can cause all kinds of weird typing errors with confusing messages. 
>
> Instead, you need to add parentheses to the **inner match** to tell the compiler what you mean:
> ```ocaml
> (* GOOD CODE *)
> match x with
> | Some y ->
>     (match
>      | Some z -> ...
>      | None -> ...)
> | None -> ...
> ```



### Problem 4

The list data structure can be used to implement a basic dictionary. If you have keys of type `'k` and values of type `'v`, then you can represent a dictionary as a list of pairs of keys and values, which has type `('k * 'v) list`.


This data structure is called the "association list" in the functional programming community. It is not the most efficient way to implement a dictionary, but it is simple and easy to understand. 

For example, the following is a dictionary of type `(int * string) list` that maps the key `1` to the value `"one"`, the key `2` to the value `"two"`, and the key `3` to the value `"three"`:
```ocaml
[(1, "one"); (2, "two"); (3, "three")]
```

Insertions can be easily implemented by prepending a new key-value pair to the list, like so:
```ocaml
let insert (k: 'k) (v: 'v) (d: ('k * 'v) list) : ('k * 'v) list =
    (k, v) :: d
```

Note that in the above code, `k` is a *variable*, whereas `'k` is a generic *type* that can be instantiated with any type such as `int`. The same goes for `v` and `'v`.

Implement the following functions:

1. `mem : ('k -> 'k -> bool) -> 'k -> ('k * 'v) list -> bool` that will check if a key is in a dictionary:
   - the first argument is the equality function for values of type `'k`
   - if the key is found, it will return `true`
   - if the key is not found, it will return `false`.
2. `lookup : ('k -> 'k -> bool) -> 'k -> ('k * 'v) list -> 'v option` that will look up a key in a dictionary:
   - the first argument is the equality function for values of type `'k`
   - if the key is found, it will return `Some v`, where `v` is the value associated with the key
   - if the key is not found, it will return `None`
   - if a dictionary has two entries with the same key (but with possibly different values), then your `lookup` should return the most recently inserted value (i.e., the left-most value).
3. `remove_key : ('k -> 'k -> bool) -> 'k -> ('k * 'v) list -> ('k * 'v) list` that will remove a given key from a dictionary (if a dictionary has multiple entries with the same key, then remove all of them).
4. `remove_value : ('v -> bool) -> ('k * 'v) list -> ('k * 'v) list` that will remove all entries whose values satisfy the given predicate `'v -> bool`.
5. `dedup : ('k -> 'k -> bool) -> ('k * 'v) list -> ('k * 'v) list` that will remove all duplicate keys from a dictionary, keeping only the most recently inserted value for each key.

For each function, in addition to including its definition, also demonstrate it works correctly with with **three distinct, non-trivial test cases and their output**.



### Problem 5

Let's implement (functional) arrays in OCaml:

```ocaml
type 'a array = ...
```

But how should we represent them?

The essence of arrays can be captured by two operations:
- `select : 'a array -> int -> 'a`, where `select a i` will read the value at index `i` in array `a`
- `store : 'a array -> int -> 'a -> 'a array`, where `store a i v` will write value `v` at index `i` in array `a`, and returning a new array with the updated value.

We say that arrays are "functional" because `store` does not modify the original array, but instead returns a new array with the updated value.

Thus, abstractly, arrays are just dictionaries that map integers to values:
```ocaml
type 'a array = Arr of (int * 'a) list
```
We will not concern ourselves about the abysmal performance of this representation, as we are only interested in the conceptual behavior of arrays.

To simplify things, we assume 
- arrays can have arbitrary lengths in both the positive and the negative direction, so negative indices are allowed.
- arrays may be non-contiguous, so you can have an array with elements at indices -74, 0, 1, 10, 100, but not at others.

Implement the following functions for arrays (try calling the functions you implemented in Problem 4 as much as possible):
- `empty: 'a array` that will return an empty array
- `select: 'a array -> int -> 'a option` that will read the value at a given index (return None if the index is not in the array)
- `store: 'a array -> int -> 'a -> 'a array` that will write a value at a given index
- `of_list: 'a list -> 'a array` that will convert a list to an array. The first element of the list will be at index 0, the second element at index 1, and so on.
- `to_list: 'a array -> 'a list` that will convert an array to a list. You should ensure that the list is in ascending order of indices. For example, the "array" `Arr [(0, "hi"); (1, "bye"); (-1, "hello"), (1, "world")]` should be converted to the list `["hello"; "hi"; "bye"]`.


The `empty`, `select`, `store` functions should satisfy the following properties:
- `select empty i` should return None for all i.
- `select (store a i v) i` should return `Some v` for all i.
- `select (store a i v) j` should return the same value as `select a j` for all `j <> i`.

In your PDF file, for each of the functions, include the definition along with **three distinct, non-trivial test cases and their output** to show that your function works correctly.



### Problem 6

The arithmetic expression of the IMP language can be easily represented in OCaml, as we have seen in the tutorial:
```ocaml
(** Arithmetic operators *)
type aop = Add | Sub | Mul

(** Arithmetic expressions *)
type aexp =
  | Int of int  (** integer constant *)
  | Aop of aop * aexp * aexp  (** arithmetic op *)
  | Var of string  (** variable *)
```

We can extend this to include boolean expressions, and the full IMP language:
```ocaml
(** Comparison ops  *)
type comp = 
  | Eq (** equal *)
  | Geq (** greater than or equal to *)
  | Gt (* greater than *)
  | Lt  (** less than *)
  | Leq (** less than or equal to *)
  | Neq (** not equal *)

(** Boolean expressions (which can appear in conditions *)
type bexp =
  (* boolean constant *)
  | Bool of bool
  (* integer comparison *)
  | Comp of comp * aexp * aexp
  | Not of bexp (* negation *)
  | And of bexp * bexp (* conjunction *)
  | Or of bexp * bexp (* disjunction *)

(** Statements *)
type stmt =
  (* assignment, aka memory write *)
  | Assign of string * aexp
  (* conditional *)
  | If of bexp * stmt * stmt
  (* while-loop *)
  | While of bexp * stmt
  (* sequence of statements *)
  | Seq of stmt * stmt
```

Parse the following IMP expressions/programs from concrete syntax to abstract syntax trees (i.e., for each string, write down an OCaml expression of type `aexp`/`bexp`/`stmt` that represents the expression/program):
- `x + y - 100`
- `1 - x >= 3`
- `true`
- `if z < z { x := 1; } else { y := 2; }`
- ```
  x := y;
  y := x; 
  z := x + y;
  ```
- ```
  while x > 0 {
    if x < 5 {
      x := x + 1;
    } else if x < 10 { 
      x := x + 2;
    } else {
      x := x - 1;
    }
  }
  ```

### Problem 7

Write a function `subst : string -> string -> aexp -> aexp` that will substitute all occurrences of a variable with another variable in an arithmetic expression. For example:
```ocaml
# subst "x" "y" (Aop (Add, Var "x", Var "y"));;
- : aexp = Aop (Add, Var "y", Var "y")
```

In your PDF file, include the function definition along with **three distinct, non-trivial test cases and their output** to show that your function works correctly.


### Problem 8

The *semantics* of a programming language feature answers the question "what happens if you run programs with said feature".

1. The semantics of `aexp` simply evaluates an arithmetic expression to an integer value. However, since we don't know the values of the variables that may appear in an `aexp`, we also need an abstract memory store -- an *abstract heap* -- to keep track of the values of variables. We can represent the abstract heap as a dictionary that maps variable names to integer values:
     ```ocaml
     type heap = Heap of (string * int) list
     ```

     Implement the function `eval_aexp : heap -> aexp -> int` that will evaluate an arithmetic expression given an abstract heap. For example:
     ```ocaml
     # eval_aexp [("x", 1); ("y", 2)] (Aop (Add, Var "x", Var "y"));;
     - : int = 3
     ```

     If a referenced variable is not found in the heap, you should call "failwith" with an appropriate error message which will crash the function.

2. The semantics of `bexp` can be defined in a similar fashion. But instead of evaluating to an integer, a boolean expression evaluates to a boolean value. Implement the function `eval_bexp : heap -> bexp -> bool` that will evaluate a boolean expression given an abstract heap. For example:
     ```ocaml
     # eval_bexp [("x", 1); ("y", 2)] (Comp (Eq, Var "x", Var "y"));;
     - : bool = false
     ```

     If a referenced variable is not found in the heap, you should call "failwith" with an appropriate error message which will crash the function.

3. The semantics of `stmt` is slightly different: a statement does not produce any value of its own; instead, given a heap memory, a statement can *modify/update* the memory. So the semantics of a statement is a function that takes a heap memory and returns a (potentially) new heap memory. Implement the function `eval_stmt : heap -> stmt -> heap` that will evaluate a statement given an abstract heap. For example:
     ```ocaml
     # eval_stmt [("x", 1); ("y", 2)] (Assign ("x", Aop (Add, Var "x", Var "y")));;
     - : heap = Heap [("x", 3); ("x", 1); ("y", 2)]
     ```
     Note that it's ok for the heap to contain entries with the same variable, as long as the left-most entry is the most recent value. So you don't need to call `dedup`.

     If a referenced variable is not found in the heap, you should call "failwith" with an appropriate error message which will crash the function.




In your PDF file, for each of the functions, include the definition along with **three distinct, non-trivial test cases and their output** to show that your function works correctly.

Finally, the following IMP program computes the 10-th Fibonacci number:
  ```
  x := 0;
  y := 1;
  n := 10;
  while (n > 0) {
    sum := x + y;
    x := y;
    y := sum;
    n := n - 1;
  }
  ```
  Run this program with an empty heap. Upon entering the `eval_stmt` function, you should print the current statement being evaluated, along with the incoming heap memory at each step. Once `eval_stmt` returns, print the final heap memory. Include the output in your PDF file.

  You can choose to format the statement and the heap however you like, as long as it is clear which statement is being evaluated and what the heap memory is at each step. You can use OCaml's format-strings to format the output, as described in the corresponding [OCaml documentation](https://v2.ocaml.org/api/Printf.html).

  *Hint:* In OCaml, to sequence a print statement with an expression, you can use the `;` operator. For example:
  ```ocaml
  (print_endline "hi"; foo 2)
  ```
  is an expression that will first print "hi" and evaluate the function call `foo 2` afterwards.

  Be extra careful if you're doing sequencing as part of an if-then-else expression:
  ```ocaml
  if true then
    print_endline "hi";
    foo 2
  else 
    print_endline "bye";
    foo 3
  ```
  is invalid, since OCaml does not know whether `foo 3` should be executed in the `else` branch, or after the whole `if-then-else` expression. You need to use parentheses to disambiguate:
  ```ocaml
  if true then (
    print_endline "hi";
    foo 2
  ) else (
    print_endline "bye";
    foo 3
  )
  ```


### Problem 9

Recall the `array` type you implemented in Problem 5. Let us augment the IMP language with arrays. The only thing we will change is to augment the `aexp` type to represent the two array operations:
```ocaml
type aexp = 
  | Int of int  (** integer constant *)
  | Aop of aop * aexp * aexp  (** arithmetic op *)
  | Var of string  (** variable *)
  | Select of aexp * aexp (** array read *)
  | Store of aexp * aexp * aexp (** array write *)
```

For example, the IMP expression `a[i][j]` will be represented as `Select (Select (Var "a", Var "i"), Var "j")`.

Array assignments need some care when they're translated from concrete syntax to abstract syntax. In imperative languages, we can write `a[i] := 1` to update the value at index `i` in array `a` to be one. 
This kind of array update syntax needs to be translated to the more basic array operations of `select` and `store`, and the IMP assignment statement.

For example, the IMP statement `a[i] := 1` can be translated to the following IMP statement:

```ocaml
Assign ("a",
  Store (Var "a", Var "i", Int 1)
)
```
That is, the variable `a` is updated with a new array whose contents are the same as the array previously referred to by `a`, except that the value at index `i` is now `1`.

And `a[i] := a[j] + 1` can be translated into the following IMP statement:
```ocaml
Assign ("a",
  Store (Var "a", Var "i", 
    Aop (Add, 
      Select (Var "a", Var "j"), 
      Int 1))
)
(* i.e., a := write(a, i, read(a, j) + 1) *)
```

For the following array assignment statements, translate them to the corresponding abstract syntax trees using a combination of `Select` and `Store`:

- `x := a[i] * a[j];`
- `y := a[a[i]];`
- `a[x - y] := z;`
- `a[i + j] := a[i] + a[j];`
- `a[a[i]] := y;`
- `a[a[i] + a[j]] := a[a[i] * a[j]];`
- `a[i][j] := a[j][i];`
- `a[i][j][k] := a[k][j][i];`



### Problem 10

In general, an array access expression like `a[i][j]...[k]` can be represented as an *access path*:
```ocaml
type path = Path of string * aexp list
```
where the first element of the tuple is the name of the array, and the second element is a list of index expressions. For example, the access path `Path ("a", [Var "i"; Aop (Add, Var "j", Int 1)])` represents the expression `a[i][j+1]`.

Recall your answer to Problem 9. You may have noticed that the same access path will get translated into different `aexp` depending on whether the path appears as the LHS of an assignment (i.e., the path is being written to), or as the RHS of an assignment (i.e., the path is being read from).

Implement the following functions in OCaml:
- `read_from_path : path -> aexp` that will convert an access path being read from to the corresponding `aexp`.
- `write_to_path : path -> aexp -> stmt` that will take a LHS access path, an RHS `aexp` that will be written to the path, and return the corresponding assignment `stmt` that will update the array at the given path with the new value.

In addition to including the definitions of these functions, also include the following tests in your PDF file:

For each abstract syntax tree you wrote down in Problem 9,

- for every access path P that is being read from (in both the RHS and the LHS of an assignment), convert it to the corresponding `aexp` using `read_from_path`, and include the output in your PDF file.
- for every access path P that is being updated with a new value, call `write_to_path` on the access path P with some dummy value (`Int 0`, for example), and include the output in your PDF file.


### Problem 11

Since arrays have been added to our language, variables can now refer to arrays, and the `eval_aexp` function may sometimes return arrays instead of integers. So we represent the possible values using the following type:
```ocaml
type value =
  | VInt of int
  | VArr of value array
```
Note that in `VArr`, the array itself recursively contains other values, which can be either integers or arrays. This allows for multi-dimensional arrays.

And heap memory is now a dictionary that maps variable names to values:
```ocaml
type heap = Heap of (string * value) list
```

Update the functions your implemented in Problem 8 to work with the new `value` type:
- `eval_aexp : heap -> aexp -> value`: reuse your array `select` and `store` functions to evaluate `Select` and `Store` expressions
- `eval_bexp : heap -> bexp -> bool`: this should be unchanged except you should call the new `eval_aexp` function
- `eval_stmt : heap -> stmt -> heap`: this should be unchanged except you should call the new `eval_aexp` and `eval_bexp` functions


Once you're done, include your code in the PDF file, and do the following:

1.  The following is the IMP program that computes the 10-th Fibonacci number using an array:
       ```
       fib[0] := 0;
       fib[1] := 1;
       n := 10;
       i := 2;
       while (i < n) {
         fib[i] := fib[i-1] + fib[i-2];
         i := i + 1;
       }
       ```

       First, translate this program into an abstract syntax tree (i.e., an OCaml expression of type `stmt`). Then, run this program with an initial heap that maps `fib` to the empty array. Upon entering the `eval_stmt` function, you should print the current statement being evaluated, along with the incoming heap memory at each step. Once `eval_stmt` returns, print the final heap memory. Include the output in your PDF file.

2. Adapt the `min2d` from HW1 into this IMP language (you may need to de-sugar access paths into `aexp`, and make function parameters into local variables). Then run the adapted program with an initial heap that maps `a` to the array `[[3; 2; 5]; []; [-1]; [7; -10; 10]]` and `min` to `100`. Print the intermediate heap memory and command at each step, and print the final heap. Your final heap should show that the local variable `min` is set to `-1`. Include the output in your PDF file.