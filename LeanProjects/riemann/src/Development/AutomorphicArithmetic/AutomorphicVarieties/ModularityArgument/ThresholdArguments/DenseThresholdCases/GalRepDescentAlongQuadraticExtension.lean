import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RankTwoDescentSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGapTwo

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Pr.RankTwoAutomorphyDescendsFromAbelianCMToRat := fun P =>
  Or.elim P.cyc2 (fun h => _root_.UpperTheory.V.Z.Bc.isAutR_of_isAutC_comp_galEmb_of_odd_quadratic_char P P.cyc h (_root_.UpperTheory.V.Z.Bc.gapTwo_alt P))
    fun h L Ω _ _ _ _ _ _ _ _ l _ ι W h1 h2 h3 h4 h5 => h L Ω l ι W h1 h2 h3 h4 h5
end
