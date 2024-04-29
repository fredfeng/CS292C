# CS292C Project 2: The Z4 SAT Solver
> 
> **Due: Monday, May 20 at 11:59pm**
> 
> This project can be done either *individually or in pairs*.


You will be implementing a SAT solver called Z4:

<img src="./z4.png" alt="drawing" width="500"/>

(Yes, Z4 -- [not Z3](https://upload.wikimedia.org/wikipedia/commons/b/b2/BMW_Z3_3.0i_Calypso_Red_2002_-_Flickr_-_The_Car_Spy_%2817%29.jpg).)

## Preparation

1. Run
   ```bash
   dune build
   ```
   You will see some error messages that complain some libraries are missing. Ignore them, and run the following:
   ```bash
   opam install . --deps-only -y
   ```
   which will automatically install the necessary dependencies.

2. Run
    ```bash
    dune build @doc
    ```
    which will build the documentation for the project. You can view the documentation by opening `_build/default/_doc/_html/index.html` in your browser. The documentation will be extremely important, since they explain what each module does and what functions are provided to you. In general, you should **not** read the code implementing the provided functions, but instead rely on the documentation to understand how to use them.

3. Review the lecture slides on DPLL and CDCL, and read through [this PDF](https://www.cs.princeton.edu/~zkincaid/courses/fall18/readings/SATHandbook-CDCL.pdf), which contains a complete description of the CDCL algorithm (more detailed than the lecture slides), as well as several extensions that are implemented in the starter code. You should carefully read this PDF, work through all contained examples, and have a good understanding of the following sections before you write any code:
   - Sections 4.1-4.5, which explains the core CDCL algorithm
   - Section 4.5.2-4.5.4, which explains important extensions that make CDCL work in practice.
    
    The starter code will use similar terminology to the PDF.


Post any questions you have in the `#proj2` Slack channel.



## Input

> Library: `Frontend`
> >
> Modules: `Var`, `Lit`, `Clause`, `Formula`
> 
> You should **not** need to understand the implementation details of any modules listed above. 


Your SAT solver will be given a file in [DIMACS CNF format](http://www.satcompetition.org/2009/format-benchmarks2009.html) as input. The parser has been provided for you in [lib/frontend](./lib/frontend/). 

The same folder contains the AST definition for the CNF format:
- variables ([lib/frontend/var.mli](./lib/frontend/var.mli))
- literals ([lib/frontend/lit.mli](./lib/frontend/lit.mli))
- clauses ([lib/frontend/clause.mli](./lib/frontend/clause.mli))
- formulas ([lib/frontend/formula.mli](./lib/frontend/formula.mli)).

Note that the type representation of variables and literals are abstract. For example, if you navigate to `Module Var` in the HTML documentation, you will see the following
```ocaml
type t
(** Type representing a variable. *)
```
This means that clients of the `Var` module has no access to how variables are implemented. Instead, they should use the public functions exposed by the module to manipulate variables. This is a common pattern in OCaml to enforce encapsulation and prevent clients from relying on the internal representation of a data structure.

The type representation of clauses and formulas, in contrast, are not abstract: clauses are sets of literals, and formulas are lists of clauses. You can directly manipulate these data structures using the functions from the [`Set`](https://ocaml.org/p/core/v0.16.1/doc/Core/Set/index.html) and the [`List`](https://ocaml.org/p/core/v0.16.1/doc/Core/List/index.html) modules of the `Base` library.


## Reference Interpreter

> Library: `Solver`
>
> Module: `Eval`
> 
> You should **not** need to understand the implementation details of, or modify, this module. 

We have provided a reference interpreter for CNF formulas in [lib/solver/eval.mli](./lib/solver/eval.mli). This module exports:
- `type u = bool option`, which represents potentially undetermined truth values.
- an abstract type `t` that represents maps from variables to their truth-values, and functions `var`, `lit`, `clause`, and `formula` that evaluate variables, literals, clauses, and formulas, respectively.




## Output

> Library: `Solver`
>
> Module: `Solution`
> 
> You should **not** need to understand the implementation details of, or modify, this module. 


If the CNF formula is satisfiable, your SAT solver should return a satisfying assignment (for enough variables to make the formula evaluate to true), and the output assignment will checked by the reference interpreter. Otherwise, your SAT solver should return UNSAT. The data type representing SAT and UNSAT can be found in [lib/solver/solution.mli](./lib/solver/solution.mli).

> Although not necessary, you can use the Z3 SMT solver as a reference. You should have Z3 installed on your machine in the first project. However, your code should **not** call Z3's APIs and let Z3 do the solving for you, which will (obviously) result in a score of 0.


## Part 1. BCP and DPLL (20 points)

> Library: `Solver`
>
> Modules: `Dpll`, `Bcp`

The file [lib/solver/dpll.ml](./lib/solver/dpll.ml) contains a complete implementation of the DPLL algorithm, minus the implementation of boolean constraint propagation (BCP), to be implemented in [lib/solver/bcp.ml](./lib/solver/bcp.ml). You should read the documentation for the `Bcp` module in the HTML documentation or in [lib/solver/bcp.mli](./lib/solver/bcp.mli) to understand what you need to implement.

Your tasks are:
1. Implement the function `val status : Eval.t -> Clause.t -> status` to determine the status of a **clause**: either satisfied (all literals evaluate to true), unsatisfied (all literals evaluate to false), unit (all but one literal evaluate to false, and the remaining literal evaluates to `None`), or unknown (none of the above). 
   
   *Hint:* You may find the following functions helpful: [`List.partition3_map`](https://ocaml.org/p/core/v0.16.1/doc/Core/List/index.html#val-partition3_map), [`Set.to_list`](https://ocaml.org/p/base/v0.16.3/doc/Base/Set/index.html#val-to_list), and `Eval.lit`.

2. Implement the function `val run : int -> Assign.t -> Clause.t list -> result * Assign.t`. This function takes as input:
   - `level`: the current decision level
   - `a`: the current assignment of type `Assign.t`
   - `cs`: the list of clauses to do BCP on.

   The assignment data structure, represented by `Assign.t`, is defined in [lib/solver/assign.mli](./lib/solver/assign.mli). You should navigate to the `Solver.Assign` module in the HTML documentation to understand what the assignment data structure looks like, and what functions are available to you. Importantly, this is a functional (i.e. immutable) data structure that keeps track of:
   1. Variable assignment of type `Eval.t`, which maps assigned variables to true or false.
   2. Decision level, which maps literals to the decision level at which they were assigned
   3. Trails, which maps each decision level to a decision literal, and the reverse-chronological list of implied literals.
   4. Implication graph, which maps each implied literal to the unit clause that implied it.
   You should not need to understand the implementation details of this data structure, but you should understand how to use it by reading the documentation.

   You won't need to *maintain* those four sub-data structures yourself; they will be updated automatically by the `Assign` module when you call the appropriate assignment functions (`Assign.assign_decision` or `Assign.assign_implied`). However, you may find it helpful to access some of those data structures through the provided interface functions, e.g., `Assign.trail`, `Assign.level`, etc., when you work on CDCL.

   Your `run` function should return
   - a `result`, which can be `Unsat c` if an unsatisfiable clause `c` is found, `Sat` if every clause evaluates to true, or `Unknown` if the function cannot determine the satisfiability of the formula.
   - an updated assignment.

   During BCP, if unit propagation of clause `c` implies that a literal `l` must be true, you should call `Assign.assign_implied a level c l` with the current assignment `a` and current `level`. This function will update all components of the assignment data structure accordingly, and return the updated data structure. 

3. Finish the implementation of the DPLL algorithm in [lib/solver/dpll.ml](./lib/solver/dpll.ml). You only need to implement the backtracking logic.
    
    **Important Notes:** 

   - The `solve` function slightly deviates from the pseudocode for the DPLL algorithm in the lecture slides: before the `solve` begins, `State.init` will choose a dummy variable (with ID=0) as the decision literal at initial decision level 0, and assign it to true, before running BCP. This is to simplify the implementation. (We can safely use 0 as a dummy variable without collision because all variables in DIMACS CNF format must be positive.)

   - Since we're doing functional programming, the input assignment is not modified after a round of BCP; instead, a new assignment is returned. Thus, when you backtrack during DPLL, you do NOT need to manually restore the assignment to its previous state. You can simply refer to the previous state using a variable that is in scope.

Everything you need to implement are stubbed with `Todo.part 1` in the starter code. You should replace these stubs with your own code.


### Testing

To test the correctness of your BCP implementation, run the DPLL solver on the set of provided benchmarks in the [test/bench](./test/bench/) folder. The benchmarks are organized into two suites: satisfiable and unsatisfiable. To run the satisfiable benchmarks, use the following command:
```bash
cd test
dune exec ./dpll_sat.exe
```

To run the unsatisfiable benchmarks, replace `dpll_sat.exe` with `dpll_unsat.exe`. Note that you must `cd test` before running the tests.

If you wish to test a specific benchmark, first go to the *root* directory of the project, and run
```bash
make install
```
This will compile the project and install an executable called `z4` in the current PATH. You can then run the executable on a specific benchmark file, e.g.
```bash
z4 <path-to-cnf-file> -s dpll
```
You can supply `-v debug` to log the intermediate steps of the solver. You can also add more log statements with `Logs.debug`.


If your solver returns a satisfying assignment, you can check its correctness by running turning on the `-c` flag (this flag will be automatically turned on if you run the unit tests):
```bash
z4 <path-to-cnf-file> -s dpll -c
```
This will tell `z4` to run the `Solver.Solution.verify_sat` function to make sure the assignment indeed makes the input formula true by evaluating the input formula using the assignment returned by your solver.

If your solver returns UNSAT, then there's no way to check whether the answer is correct, so you should not use `-c` in that case. However, we will address this problem in Parts 3 & 4.


### Scoring

Each of the two suites is worth 10 points. For each suite, you must pass all benchmarks to receive credit.



## Part 2. CDCL (20 points)

> Library: `Solver`
>
> Modules: `Cdcl`

A skeleton implementation of the CDCL algorithm is provided in [lib/solver/cdcl.ml](./lib/solver/cdcl.ml). 

Your tasks are:
1. Implement `val analyze : int -> Assign.t -> Clause.t -> Clause.t * Proof.t * int`. This function should take as input:
   - `level`: the current decision level of type `int`
   - `a`: the current assignment of type `Assign.t`
   - `c`: the unsatisfiable clause identified by BCP of type `Clause.t`

   and return:
   - a conflict clause of type `Clause.t`
   - a resolution proof of the conflict clause of type `Proof.t` (ignore this for now)
   - a `int` level to backtrack to

   As described in the lectures, you should implement first UIP learning (also explained in PDF section 4.4.1) and non-chronological backtracking (also explained in PDF section 4.4.4, under the name "Chaff clause learning").

2. Finish the implementation of the main CDCL algorithm by implementing the backtracking logic in the `solve` function.


### Notes

- Like DPLL, before `solve` begins, we choose a dummy variable (with ID=0) as the decision literal at initial decision level 0, and assign it to true.

- The provided skeleton code already implements three important extensions to the basic CDCL algorithm: restarts, clause deletion, and variable branching heuristics (implemented in [lib/solver/heuristics.mli](./lib/solver/heuristics.mli)). You should not need to modify these parts of the code. However, you should understand how they work by reading the documentation and the relevant sections in the PDF file (sections 4.5.2-4.5.4).


### Testing

Again, two suites (sat and unsat) are provided. First, `cd test`, and then run
```bash
dune exec ./cdcl_{sat,unsat}.exe
```
to test the CDCL solver on the provided CDCL benchmarks. You can also use the `z4` executable to test a specific benchmark:
```bash
make install
z4 <path-to-cnf-file> -s cdcl
```

If your solver returns a satisfying assignment, you can check its correctness by running turning on the `-c` flag:
```bash
z4 <path-to-cnf-file> -s cdcl -c
```
If your solver returns UNSAT, then there's no way to check whether the returned answer is correct, so you should not use `-c` in that case. However, we will address this problem in Parts 3 & 4.


### Scoring

Each of the two suites is worth 10 points. For each suite, you must pass all benchmarks to receive credit.





## Interlude: CS292C SAT Competition 2024 (Extra Credit)

Upon submission, your solver will automatically enter the inaugural CS292C SAT Competition 2024. Your solver will be evaluated on both correctness and performance using previously mentioned benchmarks, as well as real-world benchmarks drawn from the actual [SAT Competition](https://satcompetition.github.io/). Extra-credits will be awarded to the top solvers.





## Part 3. Proof of CDCL Unsatisfiability (10 points)

If a DPLL/CDCL solver returns UNSAT, there's nothing we can do, except to trust the solver that it has indeed exhausted the entire search space. An obvious way to eliminate the trust issue is by implementing the solver in Dafny and formally verify its correctness. However, this approach is WRONG (think about why).

There is a simpler solution: in the SAT case, the solver returns a satisfying assignment, which acts as a "certificate" and can be independently checked by a verifier that is much simpler than the solver, and hence more likely to be correct. 

Luckily, in the UNSAT case, there is also a kind of simple certificate to testify the unsatisfiability of the input formula: proofs. 

In the context of SAT solving, a proof is extremely simple: every step of the proof is either a clause in the input formula (i.e., an axiom), or an invocation of the resolution rule:
```
  a_1 \/ a_2 \/ ... \/ a_n \/ x         b_1 \/ b_2 \/ ... \/ b_m \/ -x
-------------------------------------------------------------------------
    a_1 \/ a_2 \/ ... \/ a_n \/ b_1 \/ b_2 \/ ... \/ b_m
```

A proof of unsatisfiability is simply a proof that eventually resolves into the empty clause containing zero literals, which is clearly unsatisfiable.

However, a CDCL doesn't return this proof directly. That is, it doesn't construct a giant proof tree that eventually resolves into the empty clause. Instead,
- during each conflict analysis, it constructs a small proof that resolves into a conflict clause. (This is exactly how you computed the conflict clause; the proof simply records the resolution steps you took to derive the conflict clause.) This small proof may involve resolutions of either input clauses, or previously learned conflict clauses.
- if the overall formula is UNSAT, then eventually the empty clause will be learned as a conflict.

Thus, a CDCL solver will return a proof in the following format:

```coq
Lemma conflict_1 : x1 \/ x2.
Proof.
    resolve 
        x1 \/ x2 \/ -x3
        -x3 \/ x4
        -x4 \/ x5
        -x5
Qed.

Lemma conflict_2: -x1 \/ -x2.
Proof.
    ...
Qed.

...

Theorem unsat: <empty>.
Proof.
    resolve
        x1 \/ x2
        -x1
        -x2.
Qed.
```

That is, if a CDCL solver returns UNSAT, it can simultaneously produce a *proof script* consisting of a sequence of lemmas -- which are learned conflicts and their resolution proofs -- and a main theorem `unsat` that proves the empty clause.

Your task is to augment your CDCL solver to return such a proof script when it returns UNSAT. Specifically, in your `analyze` function, extend the conflict derivation with proof construction. The data structure for proofs is defined in [lib/solver/proof.mli](./lib/solver/proof.mli). You should navigate to the `Solver.Proof` module in the HTML documentation to understand what the proof data structure looks like, and what functions are available to you. 

*Hint:* The only thing you need to do is to record the resolution steps you took to derive the conflict clause, and call appropriate functions in the `Proof` module to incrementally build up the proof. 

Once `analyze` returns the proof for the conflict clause, the `learn_conflict` function will automatically remember this proof in the background. And if your solver happens to backtrack to the initial level (which implies that the input formula is UNSAT), then the `result` functions will collect all learned conflicts and their proofs to produce a proof script of type `Script.t`. You don't need to modify any of this logic.



### Testing


The unit tests will reuse the `unsat` suite from the CDCL benchmarks. The only difference is that in addition to checking the output is UNSAT, the generated proofs will also be checked.

To run the unit tests, first, `cd test`, and then run
```bash
dune exec ./cdcl_proof.exe
```


You can also use the `z4` executable to test a specific UNSAT benchmark:
```bash
make install
z4 <path-to-cnf-file> -s cdcl -c
```
The `-c` flag will now verify the proof script returned by the solver using `Solver.Solution.verify_unsat`. This function will check that the proof script is well-formed (every claim is either an input clause, or a previously proven lemma), and that the proof script resolves into the empty clause.


### Scoring

The test suite is worth 10 points. You must pass all benchmarks to receive credit.


## Part 4. Proof of DPLL Unsatisfiability (10 points)

The DPLL solver can similarly return a unsatisfiability proof. However, the proof is much simpler than the CDCL proof, because DPLL doesn't learn conflict clauses. Instead, the proof is simply a tree of resolutions that eventually resolves into the empty clause; the proof script won't contain any lemmas.

Adapt your DPLL solver to construct such a proof when it returns UNSAT. In particular, when BCP returns UNSAT, the `make_proof` function is responsible for constructing a resolution proof of type `Proof.t`. Implement this function, so that DPLL backtracks to the initial level, the `Backtrack` exception contains a resolution proof of the empty clause. (The proof script will be constructed in the `result` function, and will contain no lemmas since DPLL doesn't learn anything.)

*Hints:*
1. Mimic the proof construction process used in CDCL, but instead employ "last UIP learning" scheme: keep resolving until the "conflict" (i.e., what the current proof resolves into) only contains *decisions literals*, and no implied literals. This will be a resolution proof of the current (partial) *decision assignment*.
2. If both branches of a decision node X are UNSAT, then each branch will return a resolution proof of the (partial) decision assignment for that branch. You can resolve these two proofs to form a resolution proof for X's (partial) decision assignment.


### Testing

The unit tests will reuse the `unsat` suite from the DPLL benchmarks suite. The only difference is that in addition to checking the output is UNSAT, the generated proofs will also be checked.

To run the unit tests, first, `cd test`, and then run
```bash
dune exec ./dpll_proof.exe
```


You can also use the `z4` executable to test a specific UNSAT benchmark:
```bash
make install
z4 <path-to-cnf-file> -s dpll -c
```

### Scoring

The test suite is worth 10 points. You must pass all benchmarks to receive credit.




## Submission

Run `make zip` to create a zip file of your project. Submit the zip file to Gradescope.
