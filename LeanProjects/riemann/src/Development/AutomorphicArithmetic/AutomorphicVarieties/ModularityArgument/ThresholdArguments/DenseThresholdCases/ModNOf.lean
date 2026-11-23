import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelRelationTwoX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RadOfDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CountE

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.J.D
theorem numJ'_alt : _root_.UpperTheory.V.Z.J.D.NumJAlt := fun hH hM hC l _ L Ω _ _ _ _ _ _ s n hn V hS h4 Q c r ι B Λ R K J _ =>
  _root_.UpperTheory.V.Z.Desc.V0.numJEDenseThresholdCases hH hM hC l L Ω s n hn V hS h4 Q c r ι B Λ R K J
theorem modularity_n_of_printed_mult_comp (hH : _root_.UpperTheory.V.Af.HypothesesH') (hM : Mult.Mult) (hC : Mult.CompOf) : _root_.UpperTheory.V.J.ModNAlt := _root_.UpperTheory.V.Z.J.D.modularity_n_of_num_j_printed_mult_comp _root_.UpperTheory.V.Z.J.D.numJ'_alt hH hM hC
end UpperTheory.V.Z.J.D
end
