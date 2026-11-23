import Mathlib
import Formalism.PeriodIntegrals.WeakApproxDVR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.BigExists

namespace PI.WA

theorem weakApproxDVR_of (hB : BigExists) (hA : Assembly) : PI.WeakApproxDVR := by
  intro E _ ι _ W Q _ _ _ _ _ _ iw p hp hpu hloc hsep x N
  choose ϖ hϖ using fun i => IsDiscreteValuationRing.exists_irreducible (W i)
  exact hA E ι W Q iw p hp hpu hloc ϖ hϖ (hB E ι W Q iw p hp hpu hloc hsep ϖ hϖ) x N

end PI.WA
