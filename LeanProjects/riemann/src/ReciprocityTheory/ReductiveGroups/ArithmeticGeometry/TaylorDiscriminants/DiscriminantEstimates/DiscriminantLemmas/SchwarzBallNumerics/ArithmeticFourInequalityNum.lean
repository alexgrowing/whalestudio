import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem arithmetic_four_inequality_num : ReciprocityTheory.ChartRestriction.G.TB.ScaledBoundInequality := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.ScaledBoundInequality
  intro P lNc D L G2 G1 hP hl hD hL hG2 hG1
  have hD0 : D ≠ 0 := by linarith
  have hcan : 2 * lNc / D * D = 2 * lNc := div_mul_cancel₀ _ hD0
  have hexp : (5 * P + 2 * lNc / D) * D * L = 5 * P * D * L + 2 * lNc * L := by
    calc (5 * P + 2 * lNc / D) * D * L = 5 * P * D * L + (2 * lNc / D * D) * L := by ring
      _ = 5 * P * D * L + 2 * lNc * L := by rw [hcan]
  rw [hexp]
  have h1 : P * G2 ≤ P * ((D + 4) * L) := mul_le_mul_of_nonneg_left hG2 hP
  have h2 : P * G1 ≤ P * (2 * L) := mul_le_mul_of_nonneg_left hG1 hP
  have h3 : 0 ≤ P * L := mul_nonneg hP (by linarith)
  have h4 : P * L ≤ P * D * L := by nlinarith [mul_nonneg h3 (sub_nonneg.mpr hD)]
  have h5 : lNc ≤ lNc * L := by nlinarith [mul_nonneg hl (sub_nonneg.mpr hL)]
  constructor <;> nlinarith

end PI.UnitaryGroupMassFormula.TBNum
