import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LcscHAOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAFTop

namespace PI.VolSemiDirect.W.Lc

theorem tensor_adele_topology_holds : TensTop := tensTop_of PI.VolStabSW.TopoAF.afTop_holds

theorem locally_compact_adelic_unitary : LcscHA := lcscHA_of tensor_adele_topology_holds

end PI.VolSemiDirect.W.Lc
