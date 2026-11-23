import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDiscriminantSquare.RelDiffTop

open NumberField

namespace PIW.CMDiscSq

theorem discSq_of (h1 : RelDiffTop) (h2 : RelDegTwo) : Formalism.L2.SG.MassRatio.DiscSq := by
  intro F E _ _ _ _ _ _ hFE
  have hN := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    F (𝓞 F) E (𝓞 E)
  rw [h1 F E hFE, Ideal.absNorm_top, one_mul, h2 F E hFE] at hN
  have hR : (((discr E).natAbs : ℕ) : ℝ) = (((discr F).natAbs : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hN
  unfold Formalism.L2.SG.MassRatio.dF
  simpa [Nat.cast_natAbs, Int.cast_abs] using hR

end PIW.CMDiscSq
