import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Closed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.EqZeroOfMemNbhdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

noncomputable section

namespace PI.VolSemiDirect.W

theorem closed_subgroup_holds : ClosedStep := closedStep_of Lc.tensor_adele_topology_holds

theorem discrete_adelic_unitary : DiscHA := discHA_of Lc.tensor_adele_topology_holds

end PI.VolSemiDirect.W
