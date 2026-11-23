import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfCV

noncomputable section

namespace PI.VolStabSW

theorem submLocal_holds : SubmLocal := submLocal_of linDens_holds changeVar_holds

theorem submDens_holds : SubmDens := submDens_of_local submLocal_holds

theorem densInf_of_coord (h : CoordInf) : DensInf := densInf_of submDens_holds h

end PI.VolStabSW
