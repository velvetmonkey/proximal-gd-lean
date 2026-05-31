/-
Proximal Gradient Descent library — Per-step Objective Decrease

Main result: one proximal GD step decreases the composite objective:
  f(x₊) + g(x₊) ≤ f(x) + g(x) − (L/2)‖x − x₊‖²
-/
import Mathlib
import ProximalGD.Defs

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-
**Per-step objective decrease for proximal gradient descent.**

Given `f` is `L`-smooth, and `x₊ = prox_{1/L,g}(x − (1/L)∇f(x))`, we have
  `f(x₊) + g(x₊) ≤ f(x) + g(x) − (L/2)‖x − x₊‖²`.

*Proof sketch.* From the prox characterisation with `z = x`:
  `g(x) ≥ g(x₊) + L⟨(x − (1/L)∇f(x) − x₊), x − x₊⟩`
       `= g(x₊) + L‖x − x₊‖² + ⟨∇f(x), x₊ − x⟩`

From L-smoothness:
  `f(x₊) ≤ f(x) + ⟨∇f(x), x₊ − x⟩ + (L/2)‖x₊ − x‖²`

Adding: `f(x₊) + g(x₊) ≤ f(x) + g(x) − (L/2)‖x − x₊‖²`.
-/
theorem prox_descent_step
    {f g : E → ℝ} {gradf : E → E} {L : ℝ} {x x' : E}
    (hL : L > 0)
    (hsmooth : IsLSmooth f gradf L)
    (hprox : IsProx g (1 / L) (x - (1 / L) • gradf x) x') :
    f x' + g x' ≤ f x + g x - L / 2 * ‖x - x'‖ ^ 2 := by
  have := hsmooth x x';
  have h_bound : g x ≥ g x' + L * ‖x - x'‖^2 + inner ℝ (gradf x) (x' - x) := by
    convert hprox x using 1 ; simp +decide [ inner_sub_left, inner_sub_right ] ; ring;
    simp +decide [ norm_sub_sq_real, inner_smul_left, hL.ne' ] ; ring;
    rw [ real_inner_comm x' x ] ; ring;
  rw [ norm_sub_rev ] at this; linarith;

end