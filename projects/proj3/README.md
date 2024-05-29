# CS292C Project 3: Certifying `z4` and `difny`
> 
> **Due: Friday, June 14 at 11:59pm**
>
> **No late days can be used** on this project, as June 14 will be the last day of the quarter.
> 
> This project can be done **either individually or in pairs**.


In this project, you will use Coq to certify (simplified versions of) `z4` and `difny`.

![](./z4-hardened.webp)

## Preparation

Run
```bash
coq_makefile -f _CoqProject *.v -o Makefile
make
```



## Submission

Turn in the following files to Gradescope:
- `SAT.v` (Part 1)
- `Imp.v`, `ImpCEvalFun.v`, `Hoare.v`, `Hoare2.v` and `HoareAsLogic.v` (Part 2)



## Part 0: Warm-up: Proof Automation in Coq (0%)

Read through "Coq Automation" section in [Imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html). You don't need to do any exercises, but understanding the automation tactics will help you a lot in the subsequent parts of this project.



## Part 1: Certifying mini-`z4` (70%)

Recall the `formula` type and the `eval` function you saw in HW5. In [SAT.v](./SAT.v), we provided the implementation of a naive SAT solver, which determines the satisfiability of a `formula` by trying all possible branches (i.e., DPLL minus BCP):

```coq
Fixpoint solve (n: var) (v: nu) (f: formula) : option nu :=
  match eval v f with
  | Some true => Some v
  | Some false => None
  | None =>
    match n with
    | 0 => None
    | S n' => 
          solve n' (v [n' |-> Some true]) f
          <|> solve n' (v [n' |-> Some false]) f
      end
  end.
```
The `solve` function takes a natural number `n`, a partial assignment `nu`, and a formula `f`, and returns an `option nu` which should be either
- `Some v'` if and only if `f` is satisfiable and `v'` satisfies f, i.e., `eval v f = Some true`.
- `None` if and only if `f` is unsatisfiable.

The logic of the `solve` function is simple: it first evaluates `f` using current partial assignment `v`:
- If the evaluation returns `Some true`, then `v` already satisfies `f`.
- If the evaluation returns `Some false`, then some decision that resulted in `v` must have been wrong, so `solve` returns `None` to signal a backtrack.
- If the evaluation returns `None`, that means that the status `f` is unknown, so we need to keep making decisions. This is where the natural number `n` comes into play: **it represents the variable that was last decided on** (at least this is true to a first approximation). Since we'll be making decisions in decreasing order of the variables, this means that
  - if `n` is `0`, then everything has been decided. It doesn't matter what we return in this case, because if everything has been decided then `f` cannot possibly evaluate to unknown. We just return a dummy `None` in this case.
  - if `n` is `S n'`, then the next variable to be assigned is `n'`. So we try solving again by setting `n'` to true or false. The notation `<|>` is for the `option_merge` function, which combines two options (with a bias towards the left).

The entry point of the solver is the `z4` function, which calls `solve` with the empty assignment and the previous assigned variable set to 1 plus the maximum variable that occurs in `f`, so that the first ever decision will be `max_var f`, the second one will be `max_var f - 1`, ..., down to `0`:
```coq
Definition z4 (f: formula) :=
  let m := max_var f in
  solve (S m) empty f.
```

Your task is to show that `z4` is a sound and complete decision procedure for the SAT problem:
```coq
Theorem z4_sound: forall f v,
  z4 f = Some v ->
  v |= f.
Proof.
Admitted.

Theorem z4_complete: forall f,
  z4 f = None ->
  forall v, ~(v |= f).
Proof.
Admitted.
```

From which you should prove that 
1. SAT is decidable, and
2. whether a formula is satisfiable is `reflect`ed by whether `z4` returns `Some` or `None`:
```coq
Definition decidable (P: Prop) : Prop := P \/ ~P.

Definition is_sat (f: formula) : Prop := 
  exists v, v |= f.

Theorem sat_dec: forall f,
  decidable (is_sat f).
Proof.
Admitted.

Definition is_some {A} (o: option A) : bool :=
  if o then true else false.

Theorem z4_spec: forall f,
  reflect (is_sat f) (is_some (z4 f)).
Proof.
Admitted.
```

To refresh yourself what `reflect` means in Coq, you may wish to refer to the section called *Case Study: Improving Reflection* from the [IndProp](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html) chapter.


To help you get started, we stated some lemmas that you may find helpful:
```coq
Lemma solve_sound: forall n v f u,
  solve n v f = Some u ->
  u |= f.
Proof.
Admitted.

Lemma solve_complete: forall n v f u,
  (forall x, x < n -> v x = None) ->
  (forall x, x >= n -> v x <> None) ->
  solve n v f = None ->
  u |_>= n = v |_>= n ->
  ~(u |= f).
Proof.
Admitted.
```
You may find `solve_sound` useful in proving `z4_sound` and `solve_complete` useful in proving `z4_complete`. However, you don't have to prove or use any provided lemmas if you choose to embark on an alternative route.


### A word on notation

Being able to quickly decipher the meaning of a Coq expression is crucial for productive proof engineering. Concise and intuitive notations can help with this. We have defined the following notations, but you're welcomed to define your own if you find them more helpful:
```coq
Notation "m '[' x '|->' v ']'" := (write m x v)
  (at level 60, v at next level, right associativity) : map_scope.
(* example: "empty[0 |-> None]" will be parsed into "write empty 0 None" *)

Notation "v |_ p" := (restrict p v) (at level 60) : map_scope.
(* example: "v |_ (fun x => is_prime x)" will be parsed into "restrict (fun x => is_prime x) v" *)

Notation "v |_> n" := (restrict (fun m => n <? m) v) (at level 60) : map_scope.
Notation "v |_>= n" := (restrict (fun m => n <=? m) v) (at level 60) : map_scope.
Notation "v |_< n" := (restrict (fun m => m <? n) v) (at level 60) : map_scope.
Notation "v |_<= n" := (restrict (fun m => m <=? n) v) (at level 60) : map_scope.

(* example: "v |_>= 3" will be parsed into "restrict (fun m => 3 <=? m) v" *)

(* example: "empty[is_prime ? Some true]" will be parsed into "overwrite empty is_prime (Some true)" *

Notation "x <|> y" := (option_merge x y) (right associativity, at level 60).
(* example: "Some 3 <|> None" will be parsed into "option_merge (Some 3) None" *)

Notation "f1 ||| f2" := (oru f1 f2) (at level 40).
Notation "f1 &&& f2" := (andu f1 f2) (at level 40).

(* v satisfies f *)
Notation "v '|=' f" := (eval v f = Some true) (at level 100).

(* v does not satisfy f *)
Notation "v '|!=' f" := (eval v f = Some false) (at level 100).

(* v may or may not satisfy f *)
Notation "v '|?=' f" := (eval v f = None) (at level 100).
```

If you're unsure about the meaning of a notation, you can always run, say, `Locate "<|>"` to see the definition of `<|>`.


### General advice

1. You're highly encourage to factor a complex proof into multiple smaller lemmas. In fact, this is necessary in some cases, because some lemmas needed to be proven by induction by themselves.
2. Whenever you see an expression of type `bool`, `bool option`, `X option`, or any non-recursive enum type, chances are you need to do a case analysis on it using `destruct`.
3. Whenever you see an integer comparison **computation** as part of your goal or the current context, like `n <? m`, `n <=? m`, `n =? m`, etc., you should consider doing a case analysis on it. In this case, you should destruct the reflection theorem of the target comparison function. For example, if you see `n <? m`, you should do `destruct (Nat.ltb_spec n m)`: this will generate two sub-goals, where in each case `n <? m` will be replaced by `true` or `false`, **and** you'll automatically get an additional **proposition** that tells you either `n < m` or `n >= m` so that `lia` can reason about `n` and `m`.


### Proof automation

Good automation is critical to maintaining your sanity when you do proof engineering in any interactive theorem prover.

To make your lives *much* easier, we have provided a magical tactic called `crush`, which is like a mini SMT solver embedded in Coq that is extremely power and can automate many tedious proofs. Specifically, crush can handle:
- Reasoning about propositional logic: `/\`, `\/`, `->`, `<->`, `~`. For this fragment of Coq, `crush` has roughly the same power as Coq's `intuition` tactic.
- Reasoning about the theory of equalities with constructors. For this fragment of Coq, `crush` has roughly the same power as Coq's `rewrite`, `discriminate`, `congruence`, and `inversion` combined.
- Reasoning about the theory of linear integer arithmetic. For this fragment of Coq, `crush` has roughly the same power as Coq's `lia` tactic.
- Limited support for instantiating universal quantifiers.

Thus, when facing a goal that you think is painfully obvious to prove, you should always try `crush` first, because it'll likely save you a lot of time. 

Even if `crush` cannot solve the goal immediately, it will often simplify the proving context significantly, so that you can then apply a couple more specialized tactics, and then `crush` again, and so on.

Here're some ways to fully maximize the power of `crush`:

- If you see an equation involving boolean-like operators, e.g., `b1 && b2 = Some true`, you should first "reflect" this equation into a proposition, e.g., `b1 = Some true /\ b2 = Some true`. Then you can use `crush`, because native `crush` cannot reason about custom operators. This is where the inversion lemmas like the ones you proved in HW5 will come especially handy. For example, `andu b1 b2 = None -> (b1 = None /\ b2 = Some true) \/ (b2 = None /\ b1 = Some true)`. You need to do this because `crush` can only `destruct` either `\/` or `/\`, not custom operators (unless you tell it to do so).

- If you want `crush` to prove equalities using rewrites, you should always structure your equations so that the RHS is strictly simpler than the LHS, since `crush` by default rewrites from left to right. Otherwise, `crush` will loop infinitely.

- When you do `induction`, be very smart about how many `intros` you do before and after `induction`. If you do too many `intros` before `induction`, your IH might be too weak for the inductive cases to proceed. If you do too few `intros`, then your IH may contain too many quantifiers for `crush` to automatically handle. Put behind quantifiers only those variables that are strictly necessary, and `intros` everything else. (If you want to adjust the order of the variables that appear in the IH, or manually make some of them quantified, you can use the `generalize dependent <VAR>` tactic.)


### Scoring 

- Task 1: `z4_sound`: 20%
- Task 2: `z4_complete`: 40%
- Task 3: `sat_dec` and `z4_spec`: 10%

For each task, you must **fully prove** the required theorems to receive credits. 

For example, the proof of `z4_sound` may **not** depend on anything that you haven't yet proven. To confirm this, you can run
```coq
Print Assumptions z4_sound.
```
to print out a list of yet-to-be-proven propositions which `z4_sound` depends on (transitively). The list should be empty for you to receive credit. The only exceptions are the following whitelist of axioms -- which you may assume without providing a proof for:

- Functional extensionality:
    ```coq
    functional_extensionality_dep : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
      (forall x : A, f x = g x) ->
      f = g
    ```
- UIP (Uniqueness of Identity Proofs), or any axiom proven equivalent to UIP in Coq's `Eqdep` module. If you use `crush`, the one that you'll mostly likely see is the following:
    ```coq
    Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p), x = eq_rect p Q x p h
    ```

These axioms are known to be unprovable in Coq, but some smart people have shown that assuming them does not break the logic of Coq either.

Importantly, assuming the law of excluded middle (LEM), or anything that is logically equivalent to or implies LEM, is **strictly forbidden**:
```coq
Axiom law_of_excluded_middle: forall (P: Prop), P \/ ~P.
```

However, you may use specific *instances* of LEM for a proposition P **provided that you have already proven P is decidable**. E.g., you can use `b = true \/ b <> true` if you have proven it already.

> If you really, really want to assume some axiom not among the whitelist (e.g., say you want to use LEM), you must write a metatheoretical proof that your axiom is consistent with Coq's logic, and submit your proof to math arXiv and a reputable journal on theorem provers. If the paper is accepted by the math/theorem proving community, we will consider allowing you to use the axiom.




## Part 2: Certifying mini-`difny` (30%)

> If you have been diligently doing past HW and projects (achieving 100% in all of them) and you have fully completed Part 1 of this project, then theoretically you will at least get A for this class (disclaimer: this is not legal advice). So Part 2 is only for those of you who want more challenge and want to aim for an A+.
>
> Consequently, you will receive credit for Part 2 **only if you got 100% in Part 1**.

Complete all exercises in the following chapters of Software Foundations:
- (5%) [Imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html) and [ImpCEvalFun](https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html).
- (10%) [Hoare](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html) from the *second* volume of Software Foundations.
- (10%) [Hoare2](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html) from the *second* volume of Software Foundations.
- (5%) [HoareAsLogic](https://softwarefoundations.cis.upenn.edu/plf-current/HoareAsLogic.html) from the *second* volume of Software Foundations.


### Scoring 

To receive the 10% credit for each item, you need to fully prove *all* exercises in the corresponding chapter(s). You must also fully complete Part 1 to receive credit for Part 2.

<!-- 
---
Once you have completed Parts 1-3, and got 100% in previous HW and projects, you will probably get an A+ for this class already. However, if you want even more challenge, read on. Or seriously, you should consult Prof. Yu Feng for potential research opportunities at this point, since you're already so deep in the Coq rabbit hole.



## Part 4: Certifying DPLL (20%)


We can adapt the `solve` function so that it calls the BCP function, which makes it the proper DPLL algorithm:
```coq
Fixpoint dpll (n: var) (v: nu) (f: formula) : option nu :=
  match bcp v f with
  | Some true => Some v
  | Some false => None
  | None =>
    match n with
    | 0 => None
    | S n' => 
        dpll n' (v [n' |-> Some true]) f
        <|> dpll n' (v [n' |-> Some false]) f
      end
  end.
```

However, this definition won't work: BCP may assign more variables, which make `n` no longer an accurate measure of what the largest, previously assigned variable is.

Even if we asked BCP to return a smaller number `m <= n` that does represent the largest, previously assigned variable, if we call `dpll` with the precessor of `m` as the first argument, it won't be **structurally recursive** anymore. Structural recursion refers to the kind of recursion that always decomposes the overall problem using the *definitional structure* of one of its arguments. For example, if the recursion is on a `list`, then a structural recursion can only recurse on the tail of the list. If you recurse on natural numbers, then structural recursion must recurse on the predecessor of `n`.

In Coq, functions defined using `Fixpoint` must be structurally recursive. So even if we as humans know that the first argument will always monotonically decrease (because BCP can only assign more variables, and can't magically make some variables "unassigned"), Coq can't infer this automatically.

There are several ways to get around this and do recursion on decreasing, but non-structurally-decreasing arguments. All of them involving proving to Coq that some argument is indeed decreasing. The most popular choices are:
1. The [`Program Fixpoint`](https://coq.inria.fr/doc/V8.18.0/refman/addendum/program.html#program-fixpoint) command.
2. The [`Function`](https://stackoverflow.com/questions/44606245) command
3. A third-party library called [Equation](https://github.com/mattam82/Coq-Equations)

You may choose any of these options to implement DPLL.

A second issue is that, even if we can show that `dpll` always decreases `n`, its first argument, the completeness lemma no longer applies! This is because the lemma requires that anything below `n` is unassigned, and anything including and above `n` is assigned. This worked previously because in `solve`, we can always split an assignment into a lower unassigned section and a higher assigned section. Both sections were always contiguous. But BCP may create "holes" in the assignment functions.

Thus, one way to do recursion and prove the completeness lemma is to use **the number of unassigned variables** as the decreasing measure.

With this in mind, your tasks are:
1. Define CNF as an `Inductive` type in Coq.
2. Implement BCP, and adapt `solve` to implement DPLL.
2. Prove that DPLL is a sound decision procedure for SAT.
3. Prove that DPLL is a complete decision procedure for SAT.

### Scoring

Talk to the TA and walk him through your implementation and proof. If you can clearly articulate your approach and the TA can understand your proofs, you'll get whatever score the TA deems appropriate. -->