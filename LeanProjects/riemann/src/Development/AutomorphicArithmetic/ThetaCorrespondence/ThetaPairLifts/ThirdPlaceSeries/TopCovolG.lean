import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TopCovolG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringGramMatrixOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAltBisStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMeasureReductionBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AnchorHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDeepCoveringLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeepGoodReductionStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatDegreeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDegreeMultiplicative
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareStatementOfKnownTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeightLowerBoundGeneral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HilbertSamuelLowerBoundOfComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ULowOfStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumCOfDeepGoodStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowOfCoverHypothesesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLowDefectBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingOfCoveringDescent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringDescentMapsCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringRankOfDescentSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringMinGenusBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FlatBoundOfAnchor
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CovolXOfStepsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAtOfGramAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringCutOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringBadLocusOfDescentSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLambdaInvariantBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreLeOfGramMeasRatStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringRationalOfLocalTraces

set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates
set_option maxHeartbeats 1000000 in
theorem topCovolG_alt_alt : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → _root_.GlobalTheory.CovTop.CovolumeBoundOfX :=
  by
  intro hSB hX hP hH hGD hQ hD
  have hS := hH.sieg
  have hK := hX.ks
  have hN := hX.lie
  have gram := _root_.GlobalTheory.T.covering_gram_of_prints hP
  have size := _root_.GlobalTheory.T.cov_size_bound
  have meas := _root_.GlobalTheory.T.covering_meas_of_prints hP
  have anc := _root_.GlobalTheory.T.anchor_bound
  have dex := _root_.GlobalTheory.T.covering_deepEx_of_prints hP
  have dg := _root_.GlobalTheory.T.deepGood_of_toroidal_and_semiabelian hP hGD hQ hS hK hN
  have fd := _root_.GlobalTheory.T.flatDeg_of_scholzeWeinstein_of_prints hP
  have deg := _root_.GlobalTheory.T.coverDegree_of_grothendieck_deformation hX hP hS hK hGD hQ hN dg size fd
  have sh := _root_.GlobalTheory.T.share_of_deep_good_size_flat_deg_cover_degree hX hP hS hK hGD hQ hN dg size fd deg
  have ht := _root_.SelfIntersectionVolumeEstimates.height_lower_bound_general_alt hSB hX hGD hQ hP hH hD dg size deg fd
  have hs := _root_.GlobalTheory.T.coverHeightSum_of_flatDeg_coverDegree_share hX hP hGD hQ hS hK hN dg size fd deg sh
  have ul := _root_.GlobalTheory.T.uniform_lower_bound_of_sums' dg size deg sh ht hs (_root_.GlobalTheory.T.sum_c_of_deep_good dg)
  have low := _root_.GlobalTheory.T.liftLowBound_of_cover_estimates size (_root_.GlobalTheory.T.lowDef_of_gram_of_anchor hP gram anc) dex dg (_root_.GlobalTheory.T.covering_ring_of_prints_gram_deepGood hP gram dg) (_root_.GlobalTheory.T.covering_maps_of_gram_deep_size_flatDeg hP hGD hQ hS hK hN gram dg size fd) (_root_.GlobalTheory.T.coverRank_of_coverDegree_and_share hX hP hGD hQ hS hK hN dg size fd deg sh) (_root_.GlobalTheory.T.covering_gmin_of_prints_gram_deep_size hP gram dg size) (_root_.GlobalTheory.T.flat_of_prints_deepGood_flatDeg_anchor hP dg fd anc) ul
  exact _root_.GlobalTheory.T.covolX_of_truncation_badSet_lambda_lowBound gram (_root_.GlobalTheory.T.lift_recursion_of_gram_bound gram) (_root_.GlobalTheory.T.liftTruncation_of_prints hP) (_root_.GlobalTheory.T.liftBadSet_of_deep_size_flatDeg_share hX hP hGD hQ hS hK hN hX.green gram dex dg size fd deg sh) (_root_.GlobalTheory.T.liftLambdaBound_of_gram_meas hP gram meas) size (_root_.GlobalTheory.T.coreLe_of_gram_meas_liftRational gram meas (_root_.GlobalTheory.T.liftRational_of_prints hP)) low
end SelfIntersectionVolumeEstimates
end
end
