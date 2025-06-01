# Final Track B: Formal Optimization for Finite Field Cryptographic Computations

## Project Background

Finite field computations over $\mathbb{F}_p$ are foundational to cryptographic systems like pairing-based protocols and zkSNARKs. In high-assurance settings, it’s crucial not only to ensure correctness but also to optimize efficiency under a well-defined cost model.

Manual optimizations—such as Montgomery arithmetic or Karatsuba tricks—can be effective but are often ad hoc and hard to verify. This project explores how such optimizations can be made automatic and formally verified. You’ll work with benchmarks from [BGMO+10], which include optimized formulas for field multiplications, squarings, and operations over tower extensions such as $\mathbb{F}_{p^{12}}$. Given a finite field expression, your goal is to build a tool that automatically derives its optimized version under different cost models.

## Motivating Example

Algorithm 9 in [BGMO+10] implements squaring over $`\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[V]/(V^2 - \xi)`$. For input $A = a_0 + a_1 V$ where $a_0, a_1 \in F_{p^2}$, the task is to compute $C = A^2 = c_0 + c_1 V$.

### Naive Version

Using basic algebra:

$$
(a_0 + a_1 V)^2 = a_0^2 + 2 a_0 a_1 V + a_1^2 \xi
$$

This expands to:

$$
\begin{aligned}
c_0 &\gets a_0^2 + a_1^2 \cdot \xi \\
c_1 &\gets 2 \cdot a_0 \cdot a_1
\end{aligned}
$$

**Operations:**

- 2 squarings in $\mathbb{F}_{p^2}$: $a_0^2$ and $a_1^2$
- 1 general multiplication in $\mathbb{F}_{p^2}$: $a_0 \cdot a_1$
- 1 multiplication between a $\mathbb{F}_{p^2}$ element and a constant $\xi$
- 1 multiplication between a $\mathbb{F}_{p^2}$ element and a constant 2
- 1 addition in $\mathbb{F}_{p^2}$

### Optimized Version

Using the identity:

$$
(a_0 + a_1)^2 - a_0^2 - a_1^2 = 2 a_0 a_1
$$

[BGMO+10] uses algebraic rewriting to avoid the general multiplication and turn the algorithm into:

$$
\begin{aligned}
t_0 &\gets a_0^2 \\
t_1 &\gets a_1^2 \\
c_0 &\gets t_1 \cdot \xi \\
c_0 &\gets c_0 + t_0 \\
c_1 &\gets a_0 + a_1 \\
c_1 &\gets c_1^2 - t_0 - t_1
\end{aligned}
$$

**Operations:**

- 3 squarings in $\mathbb{F}_{p^2}$: $a_0^2$, $a_1^2$ and $c_1^2$
- 1 multiplication between a $\mathbb{F}_{p^2}$ element and a constant $\xi$
- 2 additions in $\mathbb{F}_{p^2}$
- 2 subtractions in $\mathbb{F}_{p^2}$

### Cost Model and Cost Estimation

To compare and choose the optimal one from the above two versions, we first need a model that quantifies the cost of each individual operation. The folowing table shows a partial cost model for operations on $\mathbb{F}_{p^2}$ (please check the appendix for a full version of example cost model).

| Operation on $\mathbb{F}_{p^2}$ | Cost |
| --- | --- |
| (General Multiplication) $x \cdot y$ where $x, y \in \mathbb{F}_{p^2}$ and $x \neq y$ | 10 |
| (Squaring) $x \cdot x$ where $x \in \mathbb{F}_{p^2}$  | 6 |
| (Multiplication by Constant) $\xi \cdot x$ where $\xi, x \in \mathbb{F}_{p^2}$ and $\xi$ is a constant | 4 |
| (Addition) $x+y$ where $x, y \in \mathbb{F}_{p^2}$ | 1 |
| (Subtraction) $x-y$ where $x, y \in \mathbb{F}_{p^2}$ | 1 |
| (Inversion) $x^{-1}$ | 80 |

With the cost model at hand, we can then run a cost estimation for the two versions of algorithms.

**Cost Breakdown of the Naive Version:**

- 2 squarings: 2 × 6 = 12
- 1 general multiplication: 10
- 2 multiplications by constant: 2 × 4  = 8
- 1 addition: 1
- **Total: 31**

**Cost Beakdown of the Optimized Version:**

- 3 squarings: 3 × 6 = 18
- 1 multiplication by constant: 4
- 2 additions: 2 × 1 = 2
- 2 subtractions: 2 × 1 = 2
- **Total: 26**

Although the optimized version performs more individual operations, it avoids the expensive general multiplication. As a result, the optimized version is more computationally efficient.

Note that a cost model provides one certain perspective of how computational efficiency could be evaluated. In real-world settings, a realistic cost model should always be based on given computational resources. For example, the general multiplication of $\mathbb{F}_{p^2}$ could be dramatically reduced if specialized hardware is available, in which case the corresponding cost model would reflect a preference of such operation, yielding different optimization directions.

## Goal, Scope and Benchmarks

The goal of this project is to build a prototype that enables **cost-aware optimization** of finite field computations. For example, it should:

- **Compare** a naive expression with an optimized one for semantic equivalence;
- **Search** for lower-cost equivalents via algebraic rewrites or synthesis;
- **Evaluate** total cost using a cost model;
- **Validate** correctness and optimality of known optimizations.

You are encouraged to focus on a subset of operations (e.g., in $`\mathbb{F}_{p^4}`$, $`\mathbb{F}_{p^6}`$ or $`\mathbb{F}_{p^{12}}`$ ) to demonstrate key ideas concretely, but your approach should generalize to different given cost models.

For testing the effectiveness of your approach, we leverage the algorithms from [BGMO+10] as benchmarks. In particular, each algorithm from Algorithm 5 to Algorithm 31 show either a naive or an optimized version of a finite field expression/operation. Your approach should aim at automaitng such optimization given different cost models.

## Approaches

Your implementation can leverage a variety of formal techniques:

- **Symbolic execution** to evaluate equivalence and cost behavior;
- **Rewrite rule engines** or **equality saturation** to explore transformations;
- **SMT solvers** for algebraic reasoning and verification;
- **Proof assistants** (e.g., Lean, Coq) for full formal proofs.

Good designs will prioritize:

- **Soundness** (no incorrect rewrites)
- **Cost-awareness** (under a quantitative model)
- **Modularity** (clear separation between rewriting, costing, and checking)

## Frameworks (Feel free to use other options)

- Sketch: https://github.com/asolarlez/sketch-backend
- egg (Rust Equality-Saturation Engine): https://github.com/egraphs-good/egg
- Rosette: https://github.com/emina/rosette

## Resources

[BGMO+10] Jean-Luc Beuchat, Jorge Enrique González Díaz, Shigeo Mitsunari, Eiji Okamoto, Francisco Rodríguez-Henríquez, and Tadanori Teruya. *High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves*. Cryptology ePrint Archive, Report 2010/354, 2010. [https://eprint.iacr.org/2010/354](https://eprint.iacr.org/2010/354).

## Appendix I: Towering Structure

A *towering structure* is a step-by-step way to build more complex finite fields from simpler ones. Instead of constructing $\mathbb{F}_{p^4}$ (a degree-4 extension of a prime field $\mathbb{F}_p$) all at once, we build it gradually:

### Step 1: Build $\mathbb{F}_{p^2}$

We introduce a formal symbol $U$ to create a new number system where $U^2 = \delta$, for some fixed number $\delta$ chosen from $\mathbb{F}_p$. Typically, $\delta$ is a number that is *not* a square in $\mathbb{F}_p$, so that $U$ behaves like a "new" square root. Then:

$$
\mathbb{F}_{p^2} = \mathbb{F}_p[U]/(U^2 - \delta)
$$

This means we work with expressions like $a + bU$, where $a, b \in \mathbb{F}_p$, and use the rule $U^2 = \delta$ whenever simplifying.

### **Step 2: Build** $\mathbb{F}_{p^4}$

Now we create another extension. Let $V$ be a second formal symbol satisfying $V^2 = \xi$, where $`\xi \in \mathbb{F}_{p^2}`$ is again chosen so that $V$ represents a new square root not already in $`\mathbb{F}_{p^2}`$. We define:

```math
\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[V]/(V^2 - \xi)
```

This gives us elements of the form $a_0 + a_1 V$, where $a_0, a_1 \in \mathbb{F}_{p^2}$, and we simplify using $V^2 = \xi$.

### **Putting It Together**

If we expand each $`a_i \in \mathbb{F}_{p^2}$ as $x_i + y_i U`$, then any element in $\mathbb{F}_{p^4}$ can be written as:

```math
A = (x_0 + y_0 U) + (x_1 + y_1 U)V = x_0 + y_0 U + x_1 V + y_1 UV
```

This shows that $\mathbb{F}_{p^4}$ has a basis $\{1, U, V, UV\}$ over $\mathbb{F}_p$: every element is a linear combination of these four terms.

### Comparison: Towering vs. Flat Construction

Another way to define $\mathbb{F}_{p^4}$ is to use a single irreducible polynomial:

$$
\mathbb{F}_{p^4} = \mathbb{F}_p[X]/(P(X))
$$

where $P(X)$ is an irreducible polynomial of degree 4, such as $X^4 + X + 1$. Elements are written as:

$$
A = a_0 + a_1 X + a_2 X^2 + a_3 X^3, \quad a_i \in \mathbb{F}_p
$$

This uses the basis $\{1, X, X^2, X^3\}$ over $\mathbb{F}_p$, and also forms a 4-dimensional vector space.

### Why does $UV$ correspond to $X^3$?

In the towering structure, we built the field using two quadratic extensions. The terms 1, $U$, $V$, $UV$ naturally form four independent directions—just like 1, $X$, $X^2$, $X^3$ in the flat construction.

| **Flat Basis** | **Tower Basis** |
| --- | --- |
| 1 | 1 |
| $X$ | $V$ |
| $X^2$ | $U$ |
| $X^3$ | $UV$ |

This doesn't mean $UV = X^3$ literally—it just means that both span the highest "degree" part of the field. The symbols $U$ and $V$ are placeholders for square roots used to define field extensions, not powers in the usual sense.

### Why use towering?

1. **Modularity and Reuse**
    
    Towering lets us define $`\mathbb{F}_{p^4}`$ using previously defined field operations for $`\mathbb{F}_{p^2}`$. If we already know how to add, multiply, and invert in $`\mathbb{F}_{p^2}`$, we can reuse that when working in $`\mathbb{F}_{p^4}`$.
    
2. **Arithmetic Optimization**
    
    Check the motivating example.
    

### Take-Away

- Towering builds complex fields like $\mathbb{F}_{p^4}$ step by step using smaller fields.
- $U$ and $V$ are symbolic square roots used to define these extensions.
- $\mathbb{F}_{p^4}$ becomes a 4-dimensional space over $\mathbb{F}_p$, whether built directly (flat) or through a tower.
- Towering enables modular implementation, reuse of code, and better optimization.

## Appendix II: Example Cost Model

The following shows an example cost model for your reference.

| Operation | $\mathbb{F}_p$ | $\mathbb{F}_{p^2}$ | $\mathbb{F}_{p^4}$ | $\mathbb{F}_{p^6}$ | $\mathbb{F}_{p^{12}}$ |
| --- | --- | --- | --- | --- | --- |
| General Multiplication | 1.5 | 10 | 40 | 130 | 310 |
| Square | 1.0 | 6 | 27 | 85 | 200 |
| Multiplication by Constant | 0.8 | 4 | 15 | 50 | 120 |
| Addition/Subtraction | 0.1 | 1 | 3 | 6 | 12 |
| Inversion | 20 | 80 | 320 | 1200 | 5000 |

Note that the approach you propose should be able to accept different cost models and produce optimized version of finite field expressions accordingly.
