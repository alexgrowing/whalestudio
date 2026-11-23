import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckeLBoundedInVerticalStripsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistBaseTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomNonvanishingFromInputsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaBoundVp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearCombinationLogBoundRealInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastMemBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFEStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioValuationWithoutNormFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGaugeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomRankSumLeTwoMulTotalRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeansStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatchingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleExistenceOfThetaStatement

namespace GlobalTheory.SqTop

theorem join_claims : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  intro hHD hPr hFE hTD hTr hZD hRefl hTI hLM
  have hS := GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips
  have hInp := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hF : FieldDat := GlobalTheory.SqTop.fieldDat
  have hL : LNe := GlobalTheory.SqTop.lNe_of_functionalEquation hFE hS hF
  have hLB : LBound := GlobalTheory.T.heckeLValue_upperBound_permutedWeights_of_FE hFE hS hF
  have hTor : TorEx := GlobalTheory.ToricExist.torEx hTr hF hL
  have hBA : BetaArch := GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport hTr hF hLB hTor
  have hDE : DenEx := GlobalTheory.DenExist.denEx hZD hF
  have hDS : DenSum := GlobalTheory.DenSumPf.denSum hZD hF
  have hThb : ThbSt := GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans hTD hF hTor hDE hDS hBA
  have hBS : BotSmall := GlobalTheory.SqTop.BotSmallProof.botSmall_holds
  have hBC : BotConst := GlobalTheory.T.bottom_constant_of_theta hPr hTI hLM hInp hBS hL
  have hBE : BotEx := GlobalTheory.T.bottomPairs_exist_baseTuple hInp
  have hBET : BotExT := GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses hInp
  have hNB : NormBig := GlobalTheory.T.norm_big_of_nonvanishing hPr hInp hL
  have hRL : RhoLow := GlobalTheory.T.lValueRatio_lower_bound_gauge hTD hF hTor
  have hTri : TriEx := GlobalTheory.T.triple_existence_of_theta hHD hPr hTI hLM hL
  have hBN : BotNe := GlobalTheory.T.bottom_nonvanishing_from_inputs hPr hTI hLM hInp hL hBS hNB hTri
  have hTw : Tower := GlobalTheory.T.tower_of_theta_matching hPr hTI hLM hL
  have hOne : OneSqSt := GlobalTheory.T.square_ratio_valuation_without_norm_formula hInp hL hTor hBS hBET hNB hBN hTri hTw hBC hRefl hRL
  exact ⟨hDS, hThb, hOne, hBS, hBN, hF, hTor, hDE, hBE, hL, hTri, hTw⟩

end GlobalTheory.SqTop
