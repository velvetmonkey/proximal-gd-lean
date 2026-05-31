/-
Proximal Gradient Descent library — Proximal Operator Properties

Main result: the proximal operator is firmly nonexpansive:
  ‖prox(x) − prox(y)‖² ≤ ⟨prox(x) − prox(y), x − y⟩
-/
import Mathlib
import ProximalGD.Defs

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-
**Firmly nonexpansive property of the proximal operator.**

If `p₁ = prox_{α,g}(y₁)` and `p₂ = prox_{α,g}(y₂)` then
  `‖p₁ − p₂‖² ≤ ⟨p₁ − p₂, y₁ − y₂⟩`.

*Proof sketch.* From the prox characterisations:
  `g(p₂) ≥ g(p₁) + (1/α)⟨y₁ − p₁, p₂ − p₁⟩`
  `g(p₁) ≥ g(p₂) + (1/α)⟨y₂ − p₂, p₁ − p₂⟩`
Adding gives (after multiplying by `α > 0`)
  `0 ≥ ⟨y₁ − p₁, p₂ − p₁⟩ + ⟨y₂ − p₂, p₁ − p₂⟩`
    `= ‖p₁ − p₂‖² − ⟨y₁ − y₂, p₁ − p₂⟩`
hence `‖p₁ − p₂‖² ≤ ⟨p₁ − p₂, y₁ − y₂⟩`.
-/
theorem prox_firmly_nonexpansive
    {g : E → ℝ} {α : ℝ} (hα : α > 0)
    {y₁ y₂ p₁ p₂ : E}
    (h₁ : IsProx g α y₁ p₁) (h₂ : IsProx g α y₂ p₂) :
    ‖p₁ - p₂‖ ^ 2 ≤ ⟪p₁ - p₂, y₁ - y₂⟫ := by
  have := h₁ p₂; have := h₂ p₁; norm_num [ real_inner_comm, inner_sub_left, inner_sub_right ] at *;
  rw [ @norm_sub_sq ℝ ] ; norm_num [ real_inner_comm, real_inner_self_eq_norm_sq ] ; nlinarith [ inv_pos.2 hα, mul_inv_cancel₀ hα.ne' ] ;

end