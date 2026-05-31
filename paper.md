# proximal-gd-lean: Formal Proofs of Proximal Gradient Descent Convergence in Lean 4

Ben Cassie  
2026

## Abstract

`proximal-gd-lean` is a Lean 4 / Mathlib library formalising proximal gradient descent for composite convex optimisation. The library works over a real Hilbert space, models objectives of the form `F = f + g` with smooth convex `f` and convex possibly non-smooth `g`, defines the proximal operator through a subdifferential variational characterisation, proves firm nonexpansiveness, derives the per-step composite descent inequality, and proves the classical `O(1/k)` convergence rate. The development contains zero `sorry`, zero `admit`, and uses standard Lean/Mathlib axioms only. It provides a checked bridge between smooth gradient descent, projected gradient descent, and non-smooth composite optimisation.

## 1. Introduction

Many optimisation problems split naturally into two parts:

```text
F(x) = f(x) + g(x).
```

The function `f` is smooth and supports gradient steps. The function `g` is convex but may be non-smooth: an `l1` penalty, an indicator function of a constraint set, a nuclear norm, or another structured regulariser. Plain gradient descent cannot handle `g` directly, and the subgradient method may be slow. Proximal gradient descent takes a gradient step on `f` and then applies the proximal operator of `g`.

The proximal step is characterised variationally. For step size `alpha`,

```text
p = prox_{alpha,g}(y)
```

means

```text
(1/alpha) (y - p) in partial g(p).
```

In the library this is formalised as `IsProx`, a first-order inequality rather than a closed-form minimiser. This is the right abstraction for Lean: it covers examples such as soft-thresholding, projection, and nuclear-norm proximal maps without requiring the library to compute them explicitly.

With step size `1/L`, proximal gradient descent satisfies

```text
F(x_k) - F(x*) <= L ||x_0 - x*||^2 / (2k).
```

The library proves this rate through a Lyapunov-style induction rather than an explicit Finset-sum telescoping proof.

## 2. Library Overview

The project is organised into four implementation modules plus a root import file:

- `ProximalGD/Defs.lean` defines `IsProx`, `IsLSmooth`, `IsConvexFirstOrder`, `proxGDStep`, and `proxGDSeq`.
- `ProximalGD/ProxOperator.lean` proves firm nonexpansiveness of the proximal operator.
- `ProximalGD/Descent.lean` proves the per-step composite descent theorem.
- `ProximalGD/Convergence.lean` proves the Lyapunov inequality, objective non-increase, the inductive convergence bound, and the final `O(1/k)` theorem.
- `ProximalGD.lean` is the root module importing the library.

The project depends on Lean `v4.28.0` and Mathlib `v4.28.0`.

The definitions are first-order. `IsLSmooth` states the usual upper quadratic model for `f`. `IsConvexFirstOrder` states convexity through the gradient inequality. `IsProx` states the subdifferential characterisation of the proximal point.

## 3. Theorem Inventory

The source contains ten headline items, organised into three layers.

### Layer 1 - Definitions

1. `IsProx` — The proximal operator via subdifferential characterisation:

```text
(1/alpha)(y - p) in partial g(p).
```

2. `IsLSmooth` — L-smoothness of `f`:

```text
f(y) <= f(x) + <gradf(x), y - x> + (L/2)||y - x||^2.
```

3. `IsConvexFirstOrder` — First-order convexity:

```text
f(y) >= f(x) + <gradf(x), y - x>.
```

4. `proxGDStep / proxGDSeq` — The one-step proximal-gradient update and the full iterate sequence.

### Layer 2 - Operator and Descent

5. `prox_firmly_nonexpansive` — The proximal operator is firmly nonexpansive:

```text
||prox(x) - prox(y)||^2 <= <prox(x) - prox(y), x - y>.
```

6. `prox_descent_step` — The composite objective decreases by the squared step length:

```text
F(x_+) <= F(x) - (L/2)||x - x_+||^2.
```

This is the correct descent form for composite objectives.

### Layer 3 - Convergence

7. `per_step_lyapunov` — The one-step Lyapunov inequality:

```text
F(x_+) - F(x*) <=
  (L/2)(||x - x*||^2 - ||x_+ - x*||^2).
```

8. `objective_nonincreasing` — The composite objective is non-increasing along proximal-gradient steps:

```text
F(x_+) <= F(x).
```

9. `convergence_inductive` — The inductive convergence invariant:

```text
k * (F(x_k) - F*) <= (L/2)||x_0 - x*||^2.
```

10. `proximal_gd_convergence` — The final rate:

```text
F(x_k) - F(x*) <= L ||x_0 - x*||^2 / (2k).
```

## 4. Key Technical Highlights

### `IsProx` via Subdifferential

The proximal operator is rarely best represented by a closed form. For an indicator function it is projection; for an `l1` penalty it is soft-thresholding; for a nuclear norm it is singular-value thresholding. A single variational characterisation covers all of these cases.

In Lean, `IsProx` states the first-order condition that defines the proximal point. This lets the convergence proof depend only on the subdifferential inequality, not on any explicit formula.

### Firm Nonexpansiveness

The proximal operator is firmly nonexpansive, just like projection. This property is stronger than nonexpansiveness and is the geometric reason proximal steps are stable. The proof mirrors the projection argument but uses the subdifferential inequalities supplied by `IsProx`.

### Correct Composite Descent

For smooth gradient descent, descent is often expressed through a gradient norm. In proximal gradient descent, that is not the right quantity when `g` is nonzero. The algorithm's actual movement is the prox-corrected step, so the natural descent term is

```text
(L/2)||x - x_+||^2.
```

This distinction prevents importing an incorrect smooth-only theorem into the composite setting.

### Lyapunov Induction

Rather than proving convergence by a separate finite sum, the library proves an inductive invariant:

```text
k gap_k <= initial_energy.
```

This is a direct Lyapunov-style proof. It is concise in Lean and aligns with the objective non-increase theorem.

## 5. Relation to Sibling Libraries

`gradient-descent-lean` has DOI `10.5281/zenodo.20472996`. It is recovered from proximal gradient descent when `g = 0`.

`projected-gd-lean` is recovered when `g` is the indicator function of a closed convex set. The proximal operator is then the metric projection.

`nesterov-lean` has DOI `10.5281/zenodo.20474481`. Its accelerated counterpart for composite objectives is FISTA, which improves the rate to `O(1/k^2)` under additional structure.

`subgradient-lean` handles non-smooth objectives without proximal structure. Proximal gradient descent is faster when the non-smooth part has an efficiently characterised prox.

## 6. AI Safety Significance

Composite objectives appear throughout modern machine learning and safety-oriented optimisation: penalties, constraints, sparsity terms, robustness terms, and regularisers are often non-smooth but structured. Proximal gradient descent is a canonical model of optimisation that respects that structure.

The formal proof distinguishes what is actually needed: smoothness for `f`, convexity for both parts, the proximal variational condition, and the correct composite descent inequality. This matters for safety arguments because replacing a proximal step by an ordinary gradient step can invalidate the proof.

## 7. Conclusion

`proximal-gd-lean` formalises proximal gradient descent in Lean 4. It defines the prox operator through a subdifferential condition, proves firm nonexpansiveness, establishes composite descent, and derives the `O(1/k)` convergence theorem. It connects smooth, projected, and non-smooth optimisation in one checked framework.

## References

Moreau, J. J. (1962). *Fonctions convexes duales et points proximaux dans un espace hilbertien*. Comptes Rendus de l'Academie des Sciences, 255, 2897-2899.

Beck, A. and Teboulle, M. (2009). *A fast iterative shrinkage-thresholding algorithm for linear inverse problems*. SIAM Journal on Imaging Sciences, 2(1), 183-202.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20472996>

Cassie, B. (2026). *nesterov-lean: Formal Proofs of Nesterov Accelerated Gradient Descent in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20474481>

