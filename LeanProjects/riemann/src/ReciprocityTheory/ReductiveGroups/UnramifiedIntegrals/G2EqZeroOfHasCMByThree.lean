import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_three_sq : omegaK 3 ^ 2 = omegaK 3 - 1 := by
  have h : (((Real.sqrt (3 : ℕ) : ℝ) : ℂ)) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  unfold omegaK
  linear_combination (Complex.I ^ 2 / 4) * h + (3 / 4 : ℂ) * Complex.I_sq

def mulOmegaEquiv (L : PeriodPair) (hCM : HasCMBy 3 L) : L.lattice ≃ L.lattice where
  toFun l := ⟨omegaK 3 * l, hCM l l.2⟩
  invFun l := ⟨(l : ℂ) - omegaK 3 * l, L.lattice.sub_mem l.2 (hCM l l.2)⟩
  left_inv l := by
    apply Subtype.ext
    show omegaK 3 * (l : ℂ) - omegaK 3 * (omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq
  right_inv l := by
    apply Subtype.ext
    show omegaK 3 * ((l : ℂ) - omegaK 3 * l) = l
    linear_combination (-(l : ℂ)) * omegaK_three_sq

theorem g2_eq_zero_of_hasCMBy_three (L : PeriodPair) (hCM : HasCMBy 3 L) : L.g₂ = 0 := by
  have hsq := omegaK_three_sq
  have h4 : omegaK 3 ^ 4 = -omegaK 3 := by
    linear_combination (omegaK 3 ^ 2 + omegaK 3) * hsq
  have h0 : omegaK 3 ≠ 0 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have h1 : omegaK 3 ≠ -1 := by
    intro h
    rw [h] at hsq
    norm_num at hsq
  have key : L.G 4 = (omegaK 3 ^ 4)⁻¹ * L.G 4 := by
    conv_lhs => rw [PeriodPair.G, ← (mulOmegaEquiv L hCM).tsum_eq]
    rw [PeriodPair.G, ← tsum_mul_left]
    refine tsum_congr fun l => ?_
    show ((omegaK 3 * (l : ℂ)) ^ 4)⁻¹ = _
    rw [mul_pow, mul_inv]
  have hG : L.G 4 = 0 := by
    have h40 : omegaK 3 ^ 4 ≠ 0 := pow_ne_zero _ h0
    have h2 : omegaK 3 ^ 4 * L.G 4 = L.G 4 := by
      conv_lhs => rw [key]
      rw [mul_inv_cancel_left₀ h40]
    rw [h4] at h2
    have h3 : (omegaK 3 + 1) * L.G 4 = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (by linear_combination h) h1
    · exact h
  rw [PeriodPair.g₂, hG, mul_zero]

end ReciprocityTheory.ChartRestriction.L1
