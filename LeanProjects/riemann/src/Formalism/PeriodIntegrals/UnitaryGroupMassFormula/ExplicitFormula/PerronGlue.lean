import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronLOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ContinuousInvSqrt

namespace PI.EF

theorem perron_gluing_sides : GlueSides := by
  rintro κ _ ⟨C1, hC1, hH⟩ ⟨C2, hC2, hL⟩
  exact ⟨21 * C1 + 8 * C2, by positivity, PK.sidesBound_of hC1.le hC2.le hH hL⟩

end PI.EF
