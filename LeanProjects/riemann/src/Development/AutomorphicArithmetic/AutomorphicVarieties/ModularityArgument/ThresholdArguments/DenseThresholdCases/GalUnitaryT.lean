import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.MemOfProdEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.GdLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumHTAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumFamG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.HalfG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.RecTotT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.FrobTwT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepDirectSumAwayFromPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistLocalComponentsCompatible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Assemble
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSumTwoG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuFrobTotT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TIsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SatakeGaloisCompatibilityOfHeckeEigensystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuIrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuProdT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuSpehT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuPolG

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
namespace UpperTheory.V.Z.Win.Gu
theorem half_alt (H : _root_.UpperTheory.V.Af.HypothesesH') (hR : RowT) : HalfG := halfG UpperTheory.twist_local_components_compatible (_root_.UpperTheory.V.Z.Win.Gu.polG_of_printsH_of_rT H hR)
theorem recTotT_of_printsH (H : _root_.UpperTheory.V.Af.HypothesesH') : RecTotT := recTotT (_root_.UpperTheory.V.Z.Win.Gu.prodT_alt H extraV) (_root_.UpperTheory.V.Z.Win.Gu.spehT_alt H extraV)
theorem galUnitaryT_of_printsH_of_bcSpeh_of_rT (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) : GalUnitaryT :=
  _root_.UpperTheory.V.Z.Win.Gu.assemble_s H hB (sumFamG (_root_.UpperTheory.V.Z.Win.Gu.sumTwoG_of_printsH_gdLaws_sumAway_sumHTAt H gdLaws UpperTheory.galoisRep_direct_sum_away_from_places sumHTAt) UpperTheory.finiteSum_reduction) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness
    (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (UpperTheory.twistedDual_frobenius_compatibility (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results H.toClassicalTheorems)) (_root_.UpperTheory.satake_galois_link_of_printed_hida H) UpperTheory.satake_parameters_complex_conjugate
    (_root_.UpperTheory.V.Z.Win.Gu.irrCaseT_alt H) plainGd
theorem endShapeT' (H : _root_.UpperTheory.V.Af.HypothesesH') (hB : GlobalTheory.BcSpeh.BcSpeh) (hR : RowT) :
    type_of% (endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)) :=
  endShape_of hB (_root_.UpperTheory.satake_galois_link_of_printed_hida H) (_root_.UpperTheory.V.Z.Win.Gu.half_alt H hR) (_root_.UpperTheory.V.Z.Win.Gu.recTotT_of_printsH H) (_root_.UpperTheory.V.Z.Win.Gu.frobTotT_alt H extraV gdLaws) (frobTwT extraV gdLaws)
end UpperTheory.V.Z.Win.Gu
end
