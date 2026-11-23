import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepArith

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

section Helpers

theorem rep_H_nsmul (L : PeriodPair) (m : Type) [Fintype m] [DecidableEq m] (M : ℕ) (z : m → ℂ) :
    stdH L m (M • z) (M • z) = (M : ℂ) ^ 2 * stdH L m z z := by
  simp only [map_nsmul, LinearMap.smul_apply]
  simp only [nsmul_eq_mul]
  ring

end Helpers

end PI.UnitaryGroupMassFormula.UnimodLocStd
