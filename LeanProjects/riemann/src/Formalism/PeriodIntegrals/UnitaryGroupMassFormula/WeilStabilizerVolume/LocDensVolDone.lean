import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensVolTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensChLift

namespace PI.VolStabW

theorem volAA_holds : VolAA := volAA_of_lift chLift_holds

end PI.VolStabW
