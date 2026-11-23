import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalKernels.AsAlgApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalKernels.OfMulEps

theorem rational_kernel_division : PI.Dv.Conclusion8 := by
  intro K _ σ G _ _ T P0 hM1 EE _ _ ρE M hR
  have hF := PI.Dv.RK.eG_mem T P0 (PI.Dv.RK.tau_eps_ne T P0 hM1)
  exact ⟨PI.Dv.RK.rat_ker M P0 hF hR, PI.Dv.RK.form_eq M P0 hF⟩
