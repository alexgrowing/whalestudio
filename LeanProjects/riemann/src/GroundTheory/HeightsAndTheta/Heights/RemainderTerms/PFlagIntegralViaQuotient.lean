import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

theorem FlagIntegralViaQuotient.proof (h1 : FlagIntegralAntisymmetrize.Statement)
    (h2 : FlagIntegralVandermondeMul.Statement) : FlagIntegralViaQuotient.Statement := by
  intro f N H R hR
  have hA := h1 f N H
  rw [hR, h2 f N R] at hA
  have hne : (N.factorial : ℚ) ^ f ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linear_combination -hA

end

end RestTerms

end GroundTheory.Heights₂.Heights
