import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewform2A
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RROrdAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RROrdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutNewformAOfEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.Gal.SV
namespace UpperTheory.V.Z.Win.RR
theorem ordAway_a_alt : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAway := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAway_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem ordAbove_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAbove := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem autNewformA_of_printsH_of_repNewAE : _root_.UpperTheory.V.Af.HypothesesH' → Br.RepNewAE → AutNewformA := fun P =>
  _root_.UpperTheory.V.Z.Win.RR.autNewformA_of_exRS_of_compatT_of_repNewAE (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) (compatTOf (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) plainRec) P
end UpperTheory.V.Z.Win.RR
end
