# proximal-gd-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](ProximalGD)
[![Zenodo](https://img.shields.io/badge/Zenodo-10.5281%2Fzenodo.20476000-blue)](https://zenodo.org/records/20476000)

**proximal-gd-lean: Formal Proofs of Proximal Gradient Descent Convergence in Lean 4**

Lean 4 formal proofs of proximal gradient descent for composite convex optimisation: firm nonexpansiveness of the proximal operator, a per-step objective decrease, and an O(1/k) convergence rate.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## What this is, and why it matters

This library formalizes proximal gradient descent for a composite objective `F=f+g`. Its headline theorem, `proximal_gd_convergence`, proves a last-iterate comparison bound of `L*||x0-xstar||^2/(2*k)` for every positive iteration count.

The proof uses the correct proximal step measure rather than an ordinary gradient-norm decrease. The prox optimality inequality, smoothness of `f`, and first-order convexity give a per-step Lyapunov bound. Objective monotonicity then supports an induction that places the factor `k` in front of the final gap.

The theorem itself takes an arbitrary reference point `xstar`; interpreting the comparison as suboptimality requires choosing an actual minimizer, whose existence and optimality are not proved here. A total prox map and its `IsProx` certificate are assumed for every input. The source does not construct or compute that map, and the smoothness and convexity properties are direct hypotheses for the supplied gradient map.

## Background and motivation

Many objectives split as F = f + g, where f is smooth (a data-fit term) and g is non-smooth but structured (an ℓ₁ penalty, an indicator of a constraint set, a nuclear norm). Plain gradient descent can't touch the non-smooth part, and the subgradient method is slow. Proximal gradient descent gets the best of both: it takes a gradient step on f and then a **proximal step** on g, recovering the smooth-case O(1/k) rate while handling g exactly. It generalises both gradient descent (g = 0) and projected gradient descent (g = indicator of a convex set). This library machine-checks its convergence theory.

## Setting

A real Hilbert space `E`. The composite objective is F = f + g where f is L-smooth and convex (with gradient `gradf`) and g is convex but possibly non-smooth. The proximal operator is characterised through the subdifferential, first-order form:

```
p = prox_{α,g}(y)  ⟺  (1/α)(y − p) ∈ ∂g(p)
```

captured by the predicate `IsProx g α y p` (∀ x, g(x) ≥ g(p) + (1/α)⟨y − p, x − p⟩). The iteration `proxGDSeq` alternates a gradient step on f with a prox step on g.

## Main result

```
F(x_k) − F(x*) ≤ L·‖x₀ − x*‖² / (2k)
```

the classical **O(1/k)** rate for composite convex optimisation.

## Design note

The mathematically correct per-step decrease for proximal GD with general g is **(L/2)‖x − x₊‖²** — measured by the *step the iterate actually takes* — not the (1/(2L))‖∇f(x)‖² form familiar from smooth gradient descent. The latter only holds when g = 0; with a non-trivial prox step the gradient-norm form is wrong. Convergence is then proved by a **Lyapunov / telescoping induction** (`per_step_lyapunov` → `convergence_inductive`), avoiding explicit Finset sums.

## Project structure

```
ProximalGD/
├── Defs.lean         — IsProx, IsLSmooth, IsConvexFirstOrder, proxGDStep, proxGDSeq
├── ProxOperator.lean — prox_firmly_nonexpansive
├── Descent.lean      — prox_descent_step (per-step objective decrease)
└── Convergence.lean  — per_step_lyapunov, objective_nonincreasing,
                        convergence_inductive, proximal_gd_convergence
ProximalGD.lean       — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `IsProx` | first-order prox characterisation via the subdifferential |
| 2 | `IsLSmooth` | f(y) ≤ f(x) + ⟨∇f(x), y−x⟩ + (L/2)‖y−x‖² |
| 3 | `IsConvexFirstOrder` | f(y) ≥ f(x) + ⟨∇f(x), y−x⟩ |
| 4 | `proxGDStep` | one proximal gradient step |
| 5 | `proxGDSeq` | the proximal GD iterate sequence |
| 6 | `prox_firmly_nonexpansive` | ‖prox(x)−prox(y)‖² ≤ ⟨prox(x)−prox(y), x−y⟩ |
| 7 | `prox_descent_step` | F(x₊) ≤ F(x) − (L/2)‖x − x₊‖² |
| 8 | `per_step_lyapunov` | F(x₊) − F(x*) ≤ (L/2)(‖x−x*‖² − ‖x₊−x*‖²) |
| 9 | `objective_nonincreasing` | F(x₊) ≤ F(x) |
| 10 | `convergence_inductive` | k·(F(x_k) − F*) ≤ (L/2)‖x₀ − x*‖² |
| 11 | `proximal_gd_convergence` | F(x_k) − F(x*) ≤ L‖x₀ − x*‖²/(2k) — O(1/k) |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Paper

**proximal-gd-lean: Formal Proofs of Proximal Gradient Descent Convergence in Lean 4**
Ben Cassie (2026). Companion paper: [paper.md](paper.md).

DOI: https://doi.org/10.5281/zenodo.20476000

## Related work

- [gradient-descent-lean](https://github.com/velvetmonkey/gradient-descent-lean) — Lean 4 gradient descent convergence (O(1/k) rate)
- [projected-gd-lean](https://github.com/velvetmonkey/projected-gd-lean) — Lean 4 projected gradient descent onto convex sets (O(1/k) rate)
- [nesterov-lean](https://github.com/velvetmonkey/nesterov-lean) — Lean 4 Nesterov accelerated gradient descent (O(1/k²) rate)
- [mirror-descent-lean](https://github.com/velvetmonkey/mirror-descent-lean) — Lean 4 mirror descent with Bregman divergences (O(1/√K) rate)

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
