import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory

theorem mul_log_inv_sq_div_le_small :
    ∀ (C Λ c₀ : ℝ), 0 < c₀ → ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ →
      C * Λ * (Real.log ((s ^ 2)⁻¹) / (s ^ 2)⁻¹) ≤ s * min (c₀ / 2) (1 / 4) := by
  intro C Λ c₀ hc
  set m : ℝ := min (c₀ / 2) (1 / 4) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by norm_num)
  set K : ℝ := |C * Λ| + 1 with hK
  have hK0 : 0 < K := by positivity
  have hCK : C * Λ ≤ K := by have := le_abs_self (C * Λ); linarith
  have ha : 0 < m / (4 * K) := by positivity
  refine ⟨min (1 / 2) ((m / (4 * K)) ^ 2), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro s hs hs0
  have hs1 : s ≤ 1 / 2 := hs0.trans (min_le_left _ _)
  have hs2 : s ≤ (m / (4 * K)) ^ 2 := hs0.trans (min_le_right _ _)
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ s = t ^ 2 :=
    ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
  have ht2 : t ≤ m / (4 * K) := by
    by_contra h
    push_neg at h
    nlinarith
  have ht3 : t * (4 * K) ≤ m := (le_div_iff₀ (by positivity)).1 ht2
  have hlog : Real.log (((t ^ 2) ^ 2)⁻¹) = 4 * Real.log t⁻¹ := by
    rw [Real.log_inv, Real.log_inv, Real.log_pow, Real.log_pow]; push_cast; ring
  have hl1 : Real.log t⁻¹ ≤ t⁻¹ := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 ht); linarith
  have ht1 : t ≤ 1 := by nlinarith
  have hl0 : 0 ≤ Real.log t⁻¹ := Real.log_nonneg ((one_le_inv₀ ht).2 ht1)
  rw [hlog, div_inv_eq_mul]
  have h4 : 0 < (t ^ 2) ^ 2 := by positivity
  calc C * Λ * (4 * Real.log t⁻¹ * (t ^ 2) ^ 2)
      ≤ K * (4 * Real.log t⁻¹ * (t ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hCK (by positivity)
    _ ≤ K * (4 * t⁻¹ * (t ^ 2) ^ 2) := by gcongr
    _ = t ^ 2 * (t * (4 * K)) := by field_simp
    _ ≤ t ^ 2 * m := by gcongr

end GlobalTheory
