import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NGCong
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.FrIntGOfDelta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.NGDiff

namespace PI.CntNotIntW

theorem normG_of_loc (hL : LocDiff) (hD : DiffG) : NormG := normG_of (frIntG_of hL hD) congruence_subgroup_index

theorem normG_of_locDiff (hL : LocDiff) : NormG := normG_of_loc hL different_lattice_index

end PI.CntNotIntW
