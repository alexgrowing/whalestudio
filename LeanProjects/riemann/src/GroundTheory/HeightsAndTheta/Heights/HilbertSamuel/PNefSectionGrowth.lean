import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefShiftPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

theorem NefSectionGrowth.proof (hP : NefShiftPolynomial.Statement) (hS : ShiftSectionBound.Statement) :
    NefSectionGrowth.Statement := by
  intro K _ ι _ Ω _ _ y D a hD hV hB hN
  obtain ⟨m, r, hdeg, hcoef, hr⟩ := hP K ι Ω y D a hD hV hB hN
  obtain ⟨C, hC⟩ := hS K ι Ω y D a m hD hV hB
  set G : ℝ := (genDeg (mCoordIdeal y) D a : ℝ) / (D.factorial : ℝ) with hGdef
  have hlow : (r - Polynomial.C G * Polynomial.X ^ D).degree ≤
      (Polynomial.X ^ (D - 1) : Polynomial ℝ).degree := by
    rw [Polynomial.degree_X_pow]
    refine Polynomial.degree_le_of_natDegree_le ((Polynomial.natDegree_le_iff_coeff_eq_zero).mpr ?_)
    intro N hN'
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
    rcases eq_or_lt_of_le (show D ≤ N by omega) with h | h
    · subst h; simp [hcoef]
    · rw [if_neg (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; ring
  obtain ⟨C', hC'⟩ := (Polynomial.isBigO_atTop_of_degree_le _ _ hlow).bound
  refine ⟨|C| + C', ?_⟩
  filter_upwards [hr, hC, tendsto_natCast_atTop_atTop.eventually hC'] with n h1 h2 h3
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Real.norm_eq_abs] at h3
  have hq : 0 ≤ (n : ℝ) ^ (D - 1) := pow_nonneg (Nat.cast_nonneg n) _
  rw [abs_of_nonneg hq] at h3
  have hG : (genDeg (mCoordIdeal y) D a : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) = G * (n : ℝ) ^ D := by
    rw [hGdef]; ring
  rw [hG, abs_le]
  obtain ⟨h2a, h2b⟩ := h2
  rw [h1] at h2a h2b
  have h3' := abs_le.mp h3
  have hCq : C * (n : ℝ) ^ (D - 1) ≤ |C| * (n : ℝ) ^ (D - 1) := mul_le_mul_of_nonneg_right (le_abs_self C) hq
  constructor <;> nlinarith [h3'.1, h3'.2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
