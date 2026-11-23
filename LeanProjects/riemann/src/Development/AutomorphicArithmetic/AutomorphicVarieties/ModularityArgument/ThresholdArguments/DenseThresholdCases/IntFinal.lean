import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.IntPHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Int
theorem intP'_alt : _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Br.IntP := fun _ => intP_holds
theorem intK_of_prints : _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.IntK := fun _ => intK_holds
end UpperTheory.V.Z.Int
end
