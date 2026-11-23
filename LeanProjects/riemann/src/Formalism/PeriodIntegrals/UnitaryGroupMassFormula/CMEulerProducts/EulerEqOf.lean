import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup

open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem eulerEq_of (hF : StepFib) (hM : StepMult) (hL : StepLocal) (hR : StepRegroup) :
    EulerEq := by
  intro F E _ _ _ _ _ _ hFE M hM3
  exact hR F E M (hM E M hM3) fun v hv => hL F E M hM3 v hv (hF F E hFE v hv)

end CMEul
