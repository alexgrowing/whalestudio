import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GzNeOfTotPos

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem gS_ne : (Lat.gS D : ℚ) ≠ 0 := by
  have h0 := (D.host.g_prime 0).ne_zero
  have h1 := (D.host.g_prime 1).ne_zero
  unfold Lat.gS
  positivity

end PI.UnitaryGroupMassFormula.CntFormula
