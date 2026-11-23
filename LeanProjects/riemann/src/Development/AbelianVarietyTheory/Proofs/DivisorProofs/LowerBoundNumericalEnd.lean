import Mathlib

open scoped ComplexOrder Matrix

namespace GlobalTheory

theorem lowerBound_numerical_end :
    ∀ (ι : Type) [Fintype ι] (P h LD D1 A K rest large₂ Λ W : ℝ) (c ub s : ι → ℝ) (N C₁ C₂ C₃ : ℝ), 0 < N → 0 ≤ h → 0 ≤ LD → 0 ≤ D1 → 0 ≤ large₂ → large₂ ≤ Λ → 0 ≤ W → 0 ≤ C₁ → 0 ≤ C₂ → 0 ≤ C₃ → P = h + D1 * LD * ∑ τ, (A * c τ + K * ub τ) + rest → (∀ τ, 0 ≤ c τ ∧ c τ ≤ s τ ∧ N * |ub τ| ≤ s τ) → -A ≤ C₁ * large₂ → |K| ≤ C₂ * N * Λ → |rest| ≤ C₃ * D1 * LD * W → -(C₁ + C₂ + C₃) * D1 * LD * (Λ * ∑ τ, s τ + W) ≤ P := by
  intro ι _ P h LD D1 A K rest large₂ Λ W c ub s N C₁ C₂ C₃ hN hh hLD hD hLg hLΛ hW h1 h2 h3 hP hc hA hK hr
  have hΛ : 0 ≤ Λ := hLg.trans hLΛ
  have hA' : -A ≤ C₁ * Λ := hA.trans (mul_le_mul_of_nonneg_left hLΛ h1)
  have key : ∀ τ, -((C₁ + C₂) * Λ) * s τ ≤ A * c τ + K * ub τ := by
    intro τ
    obtain ⟨c0, cs, us⟩ := hc τ
    have e1 : -A * c τ ≤ C₁ * Λ * s τ :=
      (mul_le_mul_of_nonneg_right hA' c0).trans
        (mul_le_mul_of_nonneg_left cs (mul_nonneg h1 hΛ))
    have e2 : |K * ub τ| ≤ C₂ * Λ * s τ := by
      rw [abs_mul]
      calc |K| * |ub τ| ≤ C₂ * N * Λ * |ub τ| := mul_le_mul_of_nonneg_right hK (abs_nonneg _)
        _ = C₂ * Λ * (N * |ub τ|) := by ring
        _ ≤ C₂ * Λ * s τ := mul_le_mul_of_nonneg_left us (mul_nonneg h2 hΛ)
    have e3 := neg_abs_le (K * ub τ)
    nlinarith
  have hsum : -((C₁ + C₂) * Λ) * ∑ τ, s τ ≤ ∑ τ, (A * c τ + K * ub τ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => key τ
  have hS : 0 ≤ ∑ τ, s τ := Finset.sum_nonneg fun τ _ => (hc τ).1.trans (hc τ).2.1
  set S := ∑ τ, s τ
  set T := ∑ τ, (A * c τ + K * ub τ)
  have hM : 0 ≤ D1 * LD := mul_nonneg hD hLD
  have f1 := mul_le_mul_of_nonneg_left hsum hM
  have f2 := neg_abs_le rest
  have f3 : 0 ≤ D1 * LD * (C₃ * (Λ * S)) := by positivity
  have f4 : 0 ≤ D1 * LD * ((C₁ + C₂) * W) := by positivity
  rw [hP]
  nlinarith

end GlobalTheory
