/-
Proximal Gradient Descent library — O(1/k) Convergence Rate

Main result:
  f(xₖ) + g(xₖ) − (f(x⋆) + g(x⋆)) ≤ L‖x₀ − x⋆‖² / (2k)
-/
import Mathlib
import ProximalGD.Defs
import ProximalGD.Descent

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-! ### Per-step Lyapunov bound -/

/-
**Per-step Lyapunov bound.**
For any reference point `x⋆`,
  `f(x₊) + g(x₊) − (f(x⋆) + g(x⋆)) ≤ (L/2)(‖x − x⋆‖² − ‖x₊ − x⋆‖²)`.

*Proof sketch.* Using the prox characterisation at `z = x⋆`:
  `g(x⋆) ≥ g(x₊) + L⟨x − (1/L)∇f(x) − x₊, x⋆ − x₊⟩`

From L-smoothness:
  `f(x₊) ≤ f(x) + ⟨∇f(x), x₊ − x⟩ + (L/2)‖x₊ − x‖²`

From convexity of `f`:
  `f(x⋆) ≥ f(x) + ⟨∇f(x), x⋆ − x⟩`

Combining the f-inequalities: `f(x₊) − f(x⋆) ≤ ⟨∇f(x), x₊ − x⋆⟩ + (L/2)‖x₊ − x‖²`

Adding the g-inequality:
  `F(x₊) − F(x⋆) ≤ (L/2)‖x − x₊‖² + L⟨x − x₊, x₊ − x⋆⟩`

The right-hand side equals `(L/2)(‖x − x⋆‖² − ‖x₊ − x⋆‖²)` by the identity
  `‖a‖²/2 + ⟨a, b⟩ = (‖a + b‖² − ‖b‖²)/2`
applied with `a = x − x₊`, `b = x₊ − x⋆`.
-/
theorem per_step_lyapunov
    {f g : E → ℝ} {gradf : E → E} {L : ℝ} {x x' xstar : E}
    (hL : L > 0)
    (hsmooth : IsLSmooth f gradf L)
    (hconvex : IsConvexFirstOrder f gradf)
    (hprox : IsProx g (1 / L) (x - (1 / L) • gradf x) x') :
    f x' + g x' - (f xstar + g xstar) ≤
      L / 2 * (‖x - xstar‖ ^ 2 - ‖x' - xstar‖ ^ 2) := by
  -- From IsProx hprox at z := xstar (with α = 1/L, so 1/α = L):
  have hprox_xstar : g xstar ≥ g x' + L * inner ℝ (x - (1 / L) • gradf x - x') (xstar - x') := by
    simpa [ hL.ne' ] using hprox xstar;
  have hsmooth_xstar : f x' ≤ f x + inner ℝ (gradf x) (x' - x) + L / 2 * ‖x' - x‖ ^ 2 := by
    exact hsmooth x x'
  have hconvex_xstar : f xstar ≥ f x + inner ℝ (gradf x) (xstar - x) := by
    exact hconvex x xstar;
  simp_all +decide [ inner_sub_left, inner_sub_right, norm_sub_sq_real ];
  simp_all +decide [ inner_smul_left ];
  nlinarith [ inv_mul_cancel_left₀ hL.ne' ( inner ℝ ( gradf x ) xstar ), inv_mul_cancel_left₀ hL.ne' ( inner ℝ ( gradf x ) x' ), norm_nonneg x, norm_nonneg x', norm_nonneg xstar, real_inner_comm x xstar, real_inner_comm x' xstar, real_inner_comm x x', real_inner_self_eq_norm_sq x, real_inner_self_eq_norm_sq x', real_inner_self_eq_norm_sq xstar ]

/-! ### Objective is non-increasing -/

/-
The composite objective is non-increasing along the proximal GD sequence.
-/
theorem objective_nonincreasing
    {f g : E → ℝ} {gradf : E → E} {L : ℝ} {x x' : E}
    (hL : L > 0)
    (hsmooth : IsLSmooth f gradf L)
    (hprox : IsProx g (1 / L) (x - (1 / L) • gradf x) x') :
    f x' + g x' ≤ f x + g x := by
  exact le_trans ( prox_descent_step hL hsmooth hprox ) ( sub_le_self _ ( by positivity ) )

/-! ### Inductive convergence bound -/

/-
Key inductive bound: `k · (F(xₖ) − F⋆) ≤ (L/2) ‖x₀ − x⋆‖²`.
    Proved by induction using the Lyapunov bound and monotonicity of `F`.
-/
theorem convergence_inductive
    {f g : E → ℝ} {gradf : E → E} {prox : E → E} {L : ℝ} {x₀ xstar : E}
    (hL : L > 0)
    (hsmooth : IsLSmooth f gradf L)
    (hconvex : IsConvexFirstOrder f gradf)
    (hprox_valid : ∀ y, IsProx g (1 / L) y (prox y))
    (k : ℕ) (hk : 0 < k) :
    ↑k * (f (proxGDSeq gradf prox L x₀ k) + g (proxGDSeq gradf prox L x₀ k)
           - (f xstar + g xstar)) ≤
      L / 2 * ‖x₀ - xstar‖ ^ 2 := by
  induction' k with k ih;
  · contradiction;
  · have h_ind : ∀ k ≥ 1, k * (f (proxGDSeq gradf prox L x₀ k) + g (proxGDSeq gradf prox L x₀ k) - (f xstar + g xstar)) + L / 2 * ‖proxGDSeq gradf prox L x₀ k - xstar‖ ^ 2 ≤ L / 2 * ‖x₀ - xstar‖ ^ 2 := by
      intro k hk
      induction' hk with k hk ih;
      · have h_step : f (proxGDSeq gradf prox L x₀ 1) + g (proxGDSeq gradf prox L x₀ 1) - (f xstar + g xstar) ≤ L / 2 * (‖x₀ - xstar‖ ^ 2 - ‖proxGDSeq gradf prox L x₀ 1 - xstar‖ ^ 2) := by
          apply per_step_lyapunov hL hsmooth hconvex;
          exact hprox_valid _;
        norm_num; linarith;
      · have h_step : f (proxGDSeq gradf prox L x₀ (k + 1)) + g (proxGDSeq gradf prox L x₀ (k + 1)) - (f xstar + g xstar) ≤ L / 2 * (‖proxGDSeq gradf prox L x₀ k - xstar‖ ^ 2 - ‖proxGDSeq gradf prox L x₀ (k + 1) - xstar‖ ^ 2) := by
          apply per_step_lyapunov hL hsmooth hconvex;
          exact hprox_valid _;
        have h_step : f (proxGDSeq gradf prox L x₀ (k + 1)) + g (proxGDSeq gradf prox L x₀ (k + 1)) ≤ f (proxGDSeq gradf prox L x₀ k) + g (proxGDSeq gradf prox L x₀ k) := by
          apply objective_nonincreasing hL hsmooth;
          exact hprox_valid _;
        norm_num at * ; nlinarith;
    exact le_trans ( le_add_of_nonneg_right <| by positivity ) ( h_ind _ <| Nat.succ_pos _ )

/-! ### Main convergence theorem -/

/-
**O(1/k) convergence rate for proximal gradient descent.**

Under L-smoothness and convexity of `f`, and convexity of `g`
(captured by the prox characterisation), for any reference point `x⋆`,
  `f(xₖ) + g(xₖ) − (f(x⋆) + g(x⋆)) ≤ L ‖x₀ − x⋆‖² / (2k)`.
-/
theorem proximal_gd_convergence
    {f g : E → ℝ} {gradf : E → E} {prox : E → E} {L : ℝ} {x₀ xstar : E}
    (hL : L > 0)
    (hsmooth : IsLSmooth f gradf L)
    (hconvex : IsConvexFirstOrder f gradf)
    (hprox_valid : ∀ y, IsProx g (1 / L) y (prox y))
    (k : ℕ) (hk : 0 < k) :
    f (proxGDSeq gradf prox L x₀ k) + g (proxGDSeq gradf prox L x₀ k)
      - (f xstar + g xstar) ≤
      L * ‖x₀ - xstar‖ ^ 2 / (2 * ↑k) := by
  have := @convergence_inductive E _ _ f g gradf prox L x₀ xstar hL hsmooth hconvex hprox_valid k hk;
  rw [ le_div_iff₀ ] <;> first | positivity | linarith;

end