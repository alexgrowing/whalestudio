import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.CmSignEqOneOrNegOne
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.BottomNotUniqueHolds

namespace Formalism.L2.Th1.F2

theorem th0Witness : ThetaZeroWitness := theta_zero_witness_holds
theorem th0Ex : ThetaZeroExistence := theta_zero_exists_holds
theorem th0Uniq : ThetaZeroUniqueness := theta_zero_unique_holds
theorem normPos : NormPos := norm_pos_holds
theorem cmExample : CmExample := cm_example_holds

end Formalism.L2.Th1.F2
