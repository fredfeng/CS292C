# Final Track B: Formal Optimization for Finite Field Cryptographic Computations

## Project Background

Finite field computations over $\mathbb{F}_p$ are foundational to cryptographic systems like pairing-based protocols and zkSNARKs. In high-assurance settings, it’s crucial not only to ensure correctness but also to optimize efficiency under a well-defined cost model.

Manual optimizations—such as Montgomery arithmetic or Karatsuba tricks—can be effective but are often ad hoc and hard to verify. This project explores how such optimizations can be made **automatic and formally verified**.

You’ll work with benchmarks from Beuchat et al. (2010), which include optimized formulas for field multiplications, squarings, and operations over tower extensions such as $\mathbb{F}_{p^{12}}$. Your goal is to build a tool that automatically derives or verifies such optimizations under a specified cost model.

## Motivating Example

Algorithm 9 in Beuchat et al. implements squaring over $\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[V]/(V^2 - \xi)$. For input $A = a_0 + a_1 V$, the task is to compute $C = A^2 = c_0 + c_1 V$.

### Naive Version

Using basic algebra:

$$
(a_0 + a_1 V)^2 = a_0^2 + 2 a_0 a_1 V + a_1^2 \xi
$$

This expands to:

```
c₀ ← a₀² + a₁² · ξ
c₁ ← 2 · a₀ · a₁
```

**Operations:**

- 2 squarings $(a_0^2), (a_1^2)$
- 1 general multiplication $((a_0 \cdot a_1))$
- 1 multiplication by constant $\xi$
- 1 multiplication by constant 2
- 1 addition

### Optimized Version

Beuchat uses algebraic rewriting to avoid the general multiplication:

```
1. t₀ ← a₀²
2. t₁ ← a₁²
3. c₀ ← t₁ · ξ
4. c₀ ← c₀ + t₀
5. c₁ ← a₀ + a₁
6. c₁ ← c₁² − t₀ − t₁
```

Using the identity:

$$
(a_0 + a_1)^2 - a_0^2 - a_1^2 = 2 a_0 a_1
$$

**Operations:**

- 3 squarings $(a_0^2), (a_1^2), (a_0 + a_1)^2$
- 1 multiplication by constant $\xi$
- 2 additions, 2 subtractions

### Cost Comparison (see cost model below)

In our cost model:

- General multiplication = 10
- Squaring = 6
- Multiplication by constant = 4
- Addition/Subtraction = 1

**Naive total cost:**

- 2 squarings: 2 × 6 = 12
- 1 general multiplication: 10
- 1 multiplication by $\xi$: 4
- 1 addition: 1
- **Total: 27**

**Optimized total cost:**

- 3 squarings: 3 × 6 = 18
- 1 multiplication by $\xi$: 4
- 2 additions + 2 subtractions: 4 × 1 = 4
- **Total: 26**

Although the optimized version performs more individual operations, it avoids the expensive general multiplication. Your tool should be able to:

- Verify semantic equivalence between naive and optimized forms
- Compute and compare cost under a given model
- Justify why eliminating certain operations improves efficiency

## Project Goal and Scope

Your objective is to build a prototype that enables **formal verification and cost-aware optimization** of finite field computations. Specifically, it should:

- **Compare** a naive expression with an optimized one for semantic equivalence;
- **Search** for lower-cost equivalents via algebraic rewrites or synthesis;
- **Evaluate** total cost using a formal cost model;
- **Validate** correctness and optimality of known optimizations (e.g., from Beuchat).

You are encouraged to focus on a subset of operations (e.g., in $\mathbb{F}_{p^4}$, $\mathbb{F}_{p^6}$ or $\mathbb{F}_{p^{12}}$ ) to demonstrate key ideas concretely.

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

This project offers a practical opportunity to integrate formal reasoning with real-world cryptographic performance engineering.

## Cost Model

| Operation | Cost |
| --- | --- |
| General Multiplication | 10 |
| Squaring | 6 |
| Multiplication by Constant | 4 |
| Addition/Subtraction | 1 |

These values reflect common assumptions in cryptographic arithmetic and provide a basis for optimization.

## Tips and FAQs

(coming soon)

## Resources

[1] Beuchat et al. 2010: *High-Speed Software Implementation of the Optimal Ate Pairing over Barreto–Naehrig Curves*