# CS292C Project 1: Difny

> **Benchmarks Due: Wed, April 24 at 11:59pm**
> 
> **Implementation Due: Monday, April 29 at 11:59pm**
> 
> This is an *individual* project.


You will be implementing a verification-condition (VC) generator for a simple imperative language called Difny[^difny], which is a blend of <ins>D</ins>a<ins>fny</ins> and <ins>I</ins>MP.

<img src="./difny.png" alt="drawing" width="300"/>




## 1. Preparation

1. Please make sure you have `opam` and `dune`. Then, run
   ```bash
   dune build
   ```
   You will see some error messages that complain some libraries are missing. Ignore them, and run the following:
   ```bash
   opam install . --deps-only -y
   ```
   which will automatically install the necessary dependencies.

2. Download and install the binary for version 4.13.0 of the [Z3 SMT solver](https://github.com/Z3Prover/z3/releases). MacOS users can install Z3 using Homebrew:
   ```bash
   brew install z3
   ```
   You do not install any language bindings for Z3. The OCaml binding should have been installed in the previous step by `opam`.


3. This project will use Jane Street's `base` library, which is the de facto OCaml standard library (because OCaml's native standard library is notoriously inconsistent and encourages bad programming habits). You will see that every file in this project starts with the following line:
   ```ocaml
   open Base
   ```
   This will automatically open the `Base` module, which contains the most commonly used functions and types in OCaml. **Do not remove this line.**
   
   You can find the documentation for the `base` library [here](https://ocaml.org/p/base/v0.16.3/doc/Base/List/index.html). You may find the functions in [Base.List](https://ocaml.org/p/base/v0.16.3/doc/Base/List/index.html) especially useful for this project.

If you run into any issues, please report them in the `#tech-support` channel on Slack.



## 2. Difny Language Specification


> Difny is strictly a subset of Dafny, and a superset of IMP, so you can use your knowledge of these languages to help you understand Difny. Differences between Difny and Dafny/IMP will be highlighted.

We will first describe the concrete syntax of the Difny language using context-free grammars. Then we will go over some important semantic differences between Difny and Dafny.


### 2.0 Types

Difny has two types: `int` and `array`. An `array` type is a type constructor that takes another type as an argument. For example, `array<int>` is the type of an array of integers, and `array<array<int>>` is the type of an array of arrays of integers.

```
TYPE := "int" | "array" "<" TYPE ">"
```

Difny does not have `bool` as an explicit type, although it supports boolean expressions in conditionals.


### 2.1 Arithmetic expressions

```
AEXP := n              (* integer constant *)
      | PATH           (* memory read *)
      | "-" AEXP       (* unary minus *)
      | AEXP "+" AEXP  (* addition *)
      | AEXP "-" AEXP  (* subtraction *)
      | AEXP "*" AEXP  (* multiplication *)
      | AEXP "%" AEXP  (* modulo *)
      | "(" AEXP ")"   (* parentheses *)

PATH :=
      | id ("[" AEXP "]")* (* variable / array access *)
```

Notes:
- All binary operators are left-associative. "*" and "%" have higher precedence than "+" and "-".
- An `id` is a letter or an underscore, followed by any number of letters, digits, or underscores. It cannot start with a digit.
- The PATH non-terminal represents a memory location. It can be a simple variable `x` or an array access `x[i+1]`. Array accesses can be nested, e.g., `x[i+1][j-2][y[k]]`.



### 2.2 Boolean expressions

```
BEXP := "true"         (* true *)
      | "false"        (* false *)
      | COMP           (* comparison *)
      | "!" BEXP       (* negation *)
      | BEXP "&&" BEXP (* conjunction *)
      | BEXP "||" BEXP (* disjunction *)
      | "(" BEXP ")"   (* parentheses *)

COMP :=
      | AEXP "==" AEXP (* equality *)
      | AEXP "!=" AEXP (* inequality *)
      | AEXP "<" AEXP  (* less than *)
      | AEXP "<=" AEXP (* less than or equal to *)
      | AEXP ">" AEXP  (* greater than *)
      | AEXP ">=" AEXP (* greater than or equal to *)
```

Notes:
- Both "&&" and "||" are left-associative. "!" has higher precedence than "&&", which has higher precedence than "||".
- Comparisons are non-associative, and only integers can be compared.
- Although not stated in the grammar, consecutive comparisons are allowed. E.g., `x < y >= z == 1` will be parsed into `(x < y) && (y >= z) && (z == 1)`.



### 2.3 Formulas

`FORMULA`s form a superset of `BEXP`s, as they additionally allow quantifiers, as well as `==>` (implication) and `<==>` (if-and-only-if) as logical connectives.

```
FORMULA :=
        (* boolean constants *)
        | "true" | "false"
        (* comparison *)
        | COMP
        (* negation *)
        | "!" FORMULA
        (* logical connective *)
        | FORMULA CONN FORMULA
        (* universal quantification *)
        | "forall" id "::" FORMULA 
        (* existential quantification *)
        | "exists" id "::" FORMULA 
        (* parentheses *)
        | "(" FORMULA ")" 

CONN := "&&" | "||" | "==>" | "<==>" 
```

Notes:
- The precedence of logical connectives is as follows: "!" > "&&" > "||" > "==>" = "<==>".
- Quantification can only be made over integer variables, not arrays.
- Quantifiers have lower precedence than all the logical connectives. So `forall x :: P && Q` is equivalent to `forall x :: (P && Q)`.



### 2.4 Statements

```
STMT := 
     (* assignment *) 
     | PATH ":=" AEXP ";"
     (* conditional *) 
     | "if" BEXP "{" BLOCK "}" "else" "{" BLOCK "}" 
     (* while loop *)
     | "while" BEXP INVARIANT* "{" BLOCK "}"
     (* assertion *)
     | "assert" FORMULA ";" 
     (* assumption *)
     | "assume" FORMULA ";" 
     (* havoc (i.e. nondeterministic assignment) *)
     | id ":=" "*" ";" 
     (* method call *)
     | id ":=" id "(" ARGS ")" ";"
     (* print *)
     | "print" AEXP ";"

BLOCK := STMT*

INVARIANT := "invariant" BEXP

ARGS := any number of AEXP separated by ","
```
Notes:
- There are three kinds of "assignments":
    1. `PATH ":=" AEXP;` is a regular assignment. It updates the value of a memory location represented by `PATH` to the value of `AEXP`.
    2. `id ":=" "*";` is a havoc statement. It assigns a nondeterministic value to the variable `id`. To simplify your implementation, we disallow `PATH` to be on the left-hand side of a havoc statement.
    3. `id ":=" id "(" ARGS ");"` is a method call. Again, to simplify your implementation, method calls are always statements (i.e., they can not appear as a part of an expression), and the return value of a method is always assigned to a variable, not an arbitrary `PATH`. Note that it's easy to circumvent these restrictions in the *source program* by using temporary variables. Thus, we put slightly more burden on the programmer, and less on the parser and the verifier.
- A block is simply a sequence of statements. A block can be empty, which is equivalent to the `skip` statement in IMP.
- An `if` statement must have an `else` branch. If you want to write an `if` statement without an `else` branch, you can leave the else block empty, as in `if b { c1; c2; ... } else { }`.
- `assert`, `assume`, and `x := *` corresponds to the same commands in the guarded command language (the intermediate language that Difny will be compiled to). The reason we allow them in the surface language will become clear.


### 2.5 Methods and programs

A Difny program is a list of methods:
```
PROG := METHOD+
```

The methods have roughly the same syntax as Dafny:
```
METHOD := 
    "method" id "(" PARAMS ")" 
    "returns" "(" id ":" TYPE ")"
    REQUIRES*
    ENSURES*
    "{" 
      LOCAL*
      BLOCK
      "return" AEXP ";"
    "}"

PARAMS := a (possibly empty) list of `id ":" TYPE` separated by ","
REQUIRES := "requires" FORMULA ";"
ENSURES := "ensures" FORMULA ";"
LOCAL := "var" id ":" TYPE ";"
```

We place some syntactic restrictions to simplify your verifier implementation:
- A method must always return some value. This manifests in two ways:
    1. The method must be annotated with a return variable and its type immediately after the parameters.
    2. The method must end with a `return` statement that returns a value of the correct type. No early return is allowed (although this restriction can easily be circumvented by using extra variables and branching).
   
       If you don't need to return anything, you can do
       ```dafny
       method Foo() returns (unused: int)
       {
          ...
          return 0;
       }
       ```
- All local variables must be declared at the beginning of the method. This makes scoping trivial, as every local variable is in scope for the entirety of the method.
- The return variable named by the `returns` annotation (NOT the return statement) can appear in the `ensures` clauses, but not in `requires`. The parameter variables can appear in both `requires` and `ensures` clauses. Local variables cannot appear in `requires` or `ensures` clauses.


Finally, Difny allows `//` for single-line comments. Indentations and extra white spaces are ignored.



### 2.6 Semantic differences between Difny and Dafny

The following semantic simplifications are made in Difny to simplify the implementation of the verifier:


- Function parameters are immutable, just like in Dafny. This means that if you wish to modify a parameter, you must first copy it into a local variable, and modify the local variable instead.
- Everything in Difny is by-value, and nothing is by-reference. This includes assignments and method calls:
  - Assignments to arrays are by-value. For example, `a := b;` will copy the entire array `b` into `a`.
  - Function calls and returns are by-value. For example, in `a := f(b);`, the return value will be copied into `a`.

    Reasoning about references (and hence pointers and aliasing) is more difficult and is beyond the scope of this project.


- Arrays always have infinite length, and negative indices are allowed. That is, 'a[100]' and 'a[-9999]' always exist and, except if specified by a precondition, their value is initially undefined (like with regular variables). Although there is no way to get the length of an array, we can simulate this by having a local variable or a method parameter to represent the length of an array.


### 2.7 Examples

Example Difny programs can be found in the [examples](./examples/) directory. Note that any Difny program is a valid Dafny program.



## 3. Implementing the VC generator

We will first give an overview of the architecture of the VC generator, and align each of its components with the corresponding file/module in the skeleton code. Then, we will go over what you need to implement.

### 3.0 Roadmap

The general pipeline of the verifier is as follows:

```
Difny source program
    ||
    || I. parse
    ||
    vv  
Abstract Syntax Tree (AST)
    ||
    || II. compile
    ||
    vv
Guarded Command Language (GCL)
    ||
    || III. wp
    ||
    vv
VC Formulas
    ||
    || IV. encode
    ||
    vv
SMT constraints
    ||
    || V. solve
    ||
    vv
Either "Yes, verified",
or "No, here's an counterexample"
```

In this project, we will focus on steps II-IV; the first step, the parser, has been implemented for you, and we shall rely on an off-the-shelf SMT solver (Z3) to do the last step.

### 3.1 Alignment

The starter code for this project can be found in [lib/](./lib/). The following sections assume we're at the root of the `lib` directory.

#### Step I: parse

The lexer and the parser are provided in [lexer.mll](./lib/lexer.mll) and [menhir_parser.mly](./lib/menhir_parser.mly), respectively. You should not need to understand or modify these files.

The AST of the Difny language is defined in [lang.ml](./lib/lang.ml). In some of the constructors, we use [records](https://dev.realworldocaml.org/guided-tour.html#scrollNav-4) instead of tuples to disambiguate the meaning of each component. A record is just a tuple where each component is given a name. For example, the `meth` type which represents methods is defined as follows:

```ocaml
type meth = {
  id : string;  (** method name *)
  requires : formula list;  (** preconditions *)
  ensures : formula list;  (** postconditions *)
  ...
}
```

The same file also contains a few utility modules:
- `Syntax` defines functions to construct AST nodes (as an alternative to writing out constructors manually).
- `Utils` contains helper functions to lookup the type of a variable in a type environment.

The pretty printers for the AST are in [pretty.ml](./lib/pretty.ml).

You should not need to modify any of the files mentioned above. However, the parser does rely on [desugar.ml](./lib/desugar.ml) to translate a `path` into an `aexp` (if the path is being read from), or to an `Assign` statement if the path is being written to. You will need to copy over the code you wrote for HW2 to `desugar.ml`. Do NOT change the name of the functions there or their types in `desugar.ml`.


#### Step II: compile

Here, we will translate Difny ASTs into the guarded command language (GCL). The data type that represents GCL syntax trees is defined in [lang.ml](./lib/lang.ml) by the `gcom` data type, and the compiler itself is in [verify.ml](./lib/verify.ml). You should find the language of guarded commands exactly the same as what was covered in the lectures.

The file [verify.ml](./lib/verify.ml) is where the interesting things happen. Locate the `compile` function in the `Make` module. This function has type `stmt -> gcom list`, which means it takes a Difny statement and translates it into a list of guarded commands. You will need to fill in the implementation of this function, using the translation rules covered in the lectures.

During compilation, you may need to generate fresh variables. This can be done by calling the provided `fresh_var` function. For example, `fresh_var t ~hint:"x"` will generate a unique string `$x_<n>` where `<n>` is some internal counter, and it will also automatically record the fact that the new variable has type `t` (this info will be needed in step IV).


#### Step III: weakest pre-condition (WP)

Immediately below the `compile` function, you will find `wp : gcom -> formula -> formula` which computes the weakest pre-condition of a guarded command with respect to a given post-condition. You will need to fill in the implementation of this function using the rules covered in the lectures. You might need to generate fresh variables here, so you can use the `fresh_var` function as before.


#### Step IV: encoding VC formulas into SMT constraints

The verification condition computed by `wp` will be translated into SMT constraints. This is done in [smt.ml](./lib/smt.ml). The `aexp` and the `formula` functions translate Difny arithmetic expressions and formulas into Z3 expressions and constraints, and Difny types are converted into Z3 sorts.

#### Step V: solving

In [smt.ml](./lib/smt.ml), you will find the `check_validity` function that checks the validity of a VC formula by sending the corresponding constraints to Z3. The result of the verification is captured by the `status` type, defined at the beginning of the same file:

```ocaml
(** Status of a formula *)
type status =
  | Valid  (** formula is valid *)
  | Invalid of string  (** formula is invalid, with a counter-example *)
  | Unknown  (** formula status cannot be determined *)
```

That is, if the verification succeeds, `check_validity` will return `Valid`. If the verification fails, it will return `Invalid` with a counter-example (represented as a string). Finally, it is possible that Z3 cannot determine the status of the formula, in which case `Unknown` is returned.


### Putting it all together

The glue code is implemented by the `result` function in the `Make` module in [verify.ml](./lib/verify.ml). This function takes the Difny method passed into the `Make` module, compiles it into GCL, computes the weakest pre-condition, encodes the VC formula into SMT constraints, and then checks the validity of the constraints using Z3. The `result` function simply prints the result of the verification to the console, and returns nothing, so its return type is `unit`.


### Running the verifier

> This section assumes you're in the root of the *project* directory.

To run the verifier, first run `make install` in your terminal, which will compile the OCaml project into an executable called `difny`, and install the executable into the path so that `difny` can be run from anywhere.

You can now run
```bash
difny verify <file>
```
to verify a Difny program. This will verify each method in the program. For each method, it will print `<method_name>: verified` if the method is correct, or `<method_name>: not verified` followed by a counter-example if the method is incorrect.

(Internally, the entry point of the executable is the `go` function in [bin/main.ml](./bin/main.ml). This function invokes the `go` function in [lib/verify.ml](./lib/verify.ml), which in turn performs the five steps described above.)

The executable accepts other arguments, e.g., to set the debug level to print the intermediate results and log the execution of the verifier:

```bash
difny verify <file> -v debug
```
which sets the log level to `debug`. The default log level is `app`, which only prints the final result of the verification. Logs can be created with `Logs.debug`, `Logs.info`, `Logs.app`, etc. See [lib/verify.ml](./lib/verify.ml) for examples of how to use the logging library. The documentation for the logging library can be found [here](https://erratique.ch/software/logs).

You can run `difny --help` and `difny verify --help` to see all available commands and options. 


### What you need to implement

The only files you need to modify are `desugar.ml`, `verify.ml`, and `smt.ml`. Below is a suggested progression/leveling guide, although you are free to complete this project in any order you like.


#### Level 1: IMP

This level implements a subset of Difny that exactly corresponds to the IMP language. We make the following assumptions:

- Each method has no parameters, no `requires`, no `ensures`, and returns a dummy integer (say `0`).
- Pre- and post-conditions are specified using `assert`, `assume`, and havoc statements.
- Only integer operations are allowed. No arrays, and no method calls.

Your task is to modify `compile` and `wp` in [lib/verify.ml](./lib/verify.ml) to handle this subset of Difny by following what is covered in the lectures. The only differences between the lecture slides and this level is that we use lists to represent sequences of statements, and the empty list to represent the `Skip` statement.

Then, go to [lib/smt.ml](./lib/smt.ml), and finish the `check_validity` function by sending an appropriate formula to the solver, and based on the result of Z3 (which can be [SATISFIABLE, UNSATISFIABLE, or UNKNOWN](https://Z3prover.github.io/api/html/ml/Z3.Solver.html)), determine the status of the VC, and include a counter-example if the VC is not verified.

All the functions you need to implement are stubbed with `Todo.at_level 1`. You should replace those stubs with your own code. Feel free to define your own helper functions if you feel the need to do so.

You may find the following documentation helpful:
- Z3's [OCaml bindings](https://Z3prover.github.io/api/html/ml/Z3.html)
- Z3's [C bindings](https://Z3prover.github.io/api/html/group__capi.html) which are documented more thoroughly than the OCaml bindings

To debug your verifier, you can invoke `difny` with the `-v debug` flag to see the intermediate results of the verifier:
```bash
difny verify <file> -v debug
```

You can also add more log statements yourself. The [verify.ml](./lib/verify.ml) file contains some log statements that you can use as a reference. The documentation for the logging library can be found [here](https://erratique.ch/software/logs).

You may subdivide this level into smaller sublevels if you find it more convenient. For example, you may want to first make sure IMP programs with no loops are verified correctly, and then move on to IMP programs with loops and invariants.


#### Level 2: arrays

This level adds array support to Difny. The only changes you need to make are:
1. Copy over your code from HW2 to `desugar.ml`. You should not need to modify `compile` or `wp` for this level.
2. Go to `smt.ml` and finish the `aexp` function, and complete the translation of array `Select` and `Store` expressions into Z3 `expr`. Then, finish the implementation of `sort_of_ty` which converts a Difny type into a Z3 `sort`.
   - Z3's array theory is [documented here](https://microsoft.github.io/z3guide/docs/theories/Arrays/). The OCaml bindings for Z3 arrays are contained in the `Z3Array` module.


All the functions you need to implement are stubbed with `Todo.at_level 2`. You should replace those stubs with your own code. Feel free to define your own helper functions if you feel the need to do so.

#### Level 3: methods

This level allows a program to contain multiple methods, and each method may have any number of parameters, `requires`, and `ensures`. Method calls are also allowed, and methods can be (mutually) recursive.


Before you jump into this level, take a pause to ponder over the following question:

> To verify a loop, loop invariants are needed in order to summarize the behavior of loop, and circumvent the undecidable problem of inferring invariants automatically. 
> 
> Recursion (i.e., method definitions and calls) has exactly the same expressive power as loops. This implies some kind of "invariant" annotation is needed in order to verify methods. What is the equivalent of loop invariants for methods?

You will need to make the following changes:
1. The `verify` function in [lib/verify.ml](./lib/verify.ml) only verifies the body of a method. Now that methods can have `requires` and `ensures`, you may need to modify this function to handle those stuff as well.
2. Handle Difny's method call (represented by the `Call` constructor) in the `compile` function. *Hint*: Since recursion is allowed, inlining method calls is not a viable option. Instead, use your answer to the question above to guide your implementation.


All the functions you need to implement are stubbed with `Todo.at_level 3`. You should replace those stubs with your own code. Feel free to define your own helper functions if you feel the need to do so.



## 4. Scoring

Your total score will consist of two parts:
1. Benchmark construction (10%)
2. Verifier correctness (90%)

Your verifier will be tested on benchmarks from the following categories:

1. Difny/\IMP programs with no arrays or loops
2. Difny/\IMP programs with loops but no arrays
3. Difny/\IMP programs with both arrays and loops
4. Difny programs with non-recursive method calls
5. Difny programs with recursive method calls

where Difny/\IMP is the fragment of Difny such that a program can only contain methods with no parameters, no `requires`, no `ensures`, no method calls, and each method must return a dummy integer (say `0`).


There will be two sources of benchmarks:
1. Instructor-written benchmarks (70%):
   - Public: 50%. For each category, you must pass all of the public benchmarks to receive full credit for that category. (Hard-coding the public benchmarks will result in a score of 0.)
   - Private: 20%. Your score will be the *percentage* of private benchmarks you pass.
2. Student-written benchmarks (20%). This part consists of all of the benchmarks written by each and every one of you (described in more detail below). Your score will be the *percentage* of all student-contributed benchmarks you pass.


### Student-written benchmarks

> **Due: Wed, April 24 at 11:59pm**
> 
> No late days can be used for this part.
>
> You may continue to share benchmarks after the due date, but **only the benchmarks submitted before the due date will be considered for scoring**.


Keep the benchmarks that you use to test your code. You should submit at least 5 benchmarks, one for each category. They should be original, and should NOT be adapted from the Dafny programs that you verified in HW1 (because we have already included `min2d` and `binary_search` as part of the public instructor-written benchmark suite). 


**Do NOT copy other students' benchmarks**. This will both reduce your collective chance of scoring better in the private instructor-written benchmark suite -- since you will have fewer and less diverse public tests to work with -- and be a violation of the academic integrity policy.

Try to make your benchmarks perform interesting computation, and make sure they have non-trivial pre- and post-conditions and invariants. For example:
- You can implement your favorite array, graph, or number-theoretic algorithms, and annotate them with their specification and the necessary invariants.
- Not all of your benchmarks should be positive (verifiable). You may also want to construct negative (non-verifiable) benchmarks: e.g. take a working positive benchmark, and slightly mutate its pre- and post-conditions, or the loop invariants, to make it no longer verifiable.


We ask that you share your benchmarks in the `proj1-benchmarks` channel on Slack. We recommend posting a message in the following format for each benchmark:

```
Category: <a number between 1 - 5>
Expected verification status:
  - Method X: verified
  - Method Y: not verified
      - Reason: loop invariant is not inductive enough because ...
  - Method Z: not verified
      - Reason: pre-condition P is too weak because ...
      - Reason: loop invariant fails upon entry because ...
  - Method ...
    - Reason ...
```
Then, include the benchmark file as a whole **as a file attachment**. We suggest that you not copy and paste the code itself into the message, since it will make it hard for others to use your benchmark.


In addition to sharing your benchmarks on Slack, you should also include them in the `benchmarks` directory of your submission.

There are two ways to validate your benchmark:
1. First, you should make sure that your benchmark can be executed without runtime errors. We have provided an interpreter for Difny:
    ```bash
    difny run <file>
    ```
    which will run the Difny program and print the final values of all local variables. This can be useful for debugging your benchmarks initially.

2. To make sure that the expected verification statuses of your benchmarks are correct, you can use Dafny for validation, although you may need to enable the `--relax-definite-assignment` flag when you run Dafny on Difny programs, and ignore all array out-of-bounds errors. Dafny sometimes can infer conditions that are not explicitly stated in the program (i.e. it can be more powerful than your verifier), so use it with caution. We *may* let you run your benchmark on a reference verifier (more details soon).



## 5. Submission

Run 
```bash
make zip
```
which will create a zip file called `submission.zip` containing `lib/{desugar, verify, smt}.ml`, and the `benchmarks` directory. Upload this zip file to Gradescope.



[^difny]: (ChatGPT's rendering of the beautiful Difny language. Don't ask me what those grey hairy things are [in the original Dafny logo](https://dafny.org/images/dafny-logo.jpg)... I think they are supposed to be coconut trees?)
