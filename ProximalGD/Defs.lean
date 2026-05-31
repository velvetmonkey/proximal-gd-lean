/-
Copyright (c) 2025. All rights reserved.
Proximal Gradient Descent library — Core Definitions

Setting: composite optimisation  min f(x) + g(x)
  • f : E → ℝ   L-smooth and convex
  • g : E → ℝ   convex, proper, lower-semicontinuous (possibly non-smooth)
  • E : real Hilbert space
-/
import Mathlib

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- convenient local notation for the real inner product
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-! ## Proximal operator -/

/-- First-order optimality characterisation of the proximal operator.

`IsProx g α y p` means `p = prox_{α,g}(y)`, equivalently
`(1/α)(y − p) ∈ ∂g(p)`, i.e. for every `x`,
  `g(x) ≥ g(p) + (1/α)⟨y − p, x − p⟩`. -/
def IsProx (g : E → ℝ) (α : ℝ) (y p : E) : Prop :=
  ∀ x : E, g x ≥ g p + (1 / α) * ⟪y - p, x - p⟫

/-! ## Smoothness and convexity -/

/-- L-smoothness (descent lemma for the gradient):
  `f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2)‖y − x‖²`. -/
def IsLSmooth (f : E → ℝ) (gradf : E → E) (L : ℝ) : Prop :=
  ∀ x y : E, f y ≤ f x + ⟪gradf x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2

/-- First-order convexity condition:
  `f(y) ≥ f(x) + ⟨∇f(x), y − x⟩`. -/
def IsConvexFirstOrder (f : E → ℝ) (gradf : E → E) : Prop :=
  ∀ x y : E, f y ≥ f x + ⟪gradf x, y - x⟫

/-! ## Proximal gradient descent iteration -/

/-- One step of proximal gradient descent:
  `x₊ = prox_{1/L, g}(x − (1/L)∇f(x))`. -/
def proxGDStep (gradf : E → E) (prox : E → E) (L : ℝ) (x : E) : E :=
  prox (x - (1 / L) • gradf x)

/-- The proximal GD sequence starting from `x₀`. -/
def proxGDSeq (gradf : E → E) (prox : E → E) (L : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | n + 1 => proxGDStep gradf prox L (proxGDSeq gradf prox L x₀ n)

end
