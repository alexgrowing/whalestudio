import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensChLift

namespace PI.VolStabS

theorem volAA_holds : VolAA := volAA_of_lift chLift_holds

end PI.VolStabS
