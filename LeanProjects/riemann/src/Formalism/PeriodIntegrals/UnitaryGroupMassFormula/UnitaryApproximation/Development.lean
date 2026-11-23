import Mathlib
import Formalism.PeriodIntegrals.UnitaryApproxFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryApproximation.WeakApproxF

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFinWork

def TopStep : Prop := CayleyFin → EigAvoid → PI.UnitaryApproxFin.UnitaryApproxFin
def CayleyStep : Prop := ApproxE → BddR → UnitS → CayleyFin
def ApproxEStep : Prop := WeakApproxF → ApproxE

theorem unitaryApproxFin_of (h1 : TopStep) (h2 : CayleyStep) (h3 : ApproxEStep)
    (hW : WeakApproxF) (hB : BddR) (hU : UnitS) (hE : EigAvoid) :
    PI.UnitaryApproxFin.UnitaryApproxFin :=
  h1 (h2 (h3 hW) hB hU) hE

end PI.UnitaryApproxFinWork

end
