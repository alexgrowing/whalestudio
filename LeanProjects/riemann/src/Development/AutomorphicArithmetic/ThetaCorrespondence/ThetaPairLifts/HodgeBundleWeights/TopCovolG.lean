import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.NefModelVolumes.TopCovolG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringGramMatrixOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringMeasureReductionBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsDeepCoveringLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DeepGoodReductionStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatDegreeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDegreeMultiplicative
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShareStatementOfKnownTheorems
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightLowerBoundGeneral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HilbertSamuelLowerBoundOfComponents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringLowDefectBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RingOfCoveringDescent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDescentMapsCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringRankOfDescentSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringMinGenusBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatAtOfSplitCovering
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringCutOfLocalTraces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringBadLocusOfDescentSteps
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringLambdaInvariantBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringRationalOfLocalTraces

section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates
set_option maxHeartbeats 1000000 in
theorem topCovolG_alt : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → CovolX :=
  by
  intro hSB hX hP hH hGD hQ hD
  have hS := hH.sieg
  have hK := hX.ks
  have hN := hX.lie
  have gram := _root_.GlobalTheory.T.covering_gram_matrix_criterion hP
  have size := GlobalTheory.T.size_bound_statement
  have meas := _root_.GlobalTheory.T.covering_measure_reduction_bound hP
  have anc := GlobalTheory.T.anchor_bound_statement
  have dex := _root_.GlobalTheory.T.covering_deep_level_exists hP
  have dg := _root_.GlobalTheory.T.deepGood_of_published_inputs hP hGD hQ hS hK hN
  have fd := _root_.GlobalTheory.T.flatDeg_of_scholze_weinstein hP
  have deg := _root_.GlobalTheory.T.covering_degree_multiplicative hX hP hS hK hGD hQ hN dg size fd
  have sh := _root_.GlobalTheory.T.share_of_prints_deg_flatDeg hX hP hS hK hGD hQ hN dg size fd deg
  have ht := _root_.SelfIntersectionVolumeEstimates.height_lower_bound_general hSB hX hGD hQ hP hH hD dg size deg fd
  have hs := _root_.GlobalTheory.T.hilbertSamuel_lower_bound_of_components hX hP hGD hQ hS hK hN dg size fd deg sh
  have ul := GlobalTheory.T.uniform_lower_bound_of_sums dg size deg sh ht hs (GlobalTheory.T.sum_constant_of_deep_good dg)
  have low := GlobalTheory.T.lower_bound_of_all_estimates size (_root_.GlobalTheory.T.covering_low_defect_bound hP gram anc) dex dg (_root_.GlobalTheory.T.covering_ring_descent hP gram dg) (_root_.GlobalTheory.T.covering_descent_maps_exist hP hGD hQ hS hK hN gram dg size fd) (_root_.GlobalTheory.T.covering_rank_formula hX hP hGD hQ hS hK hN dg size fd deg sh) (_root_.GlobalTheory.T.covering_min_genus_eq hP gram dg size) (_root_.GlobalTheory.T.flat_of_anchor hP dg fd anc) ul
  exact GlobalTheory.T.covolume_from_gram_and_bounds gram (GlobalTheory.T.recursion_of_gram_bound gram) (_root_.GlobalTheory.T.covering_cut_criterion hP) (_root_.GlobalTheory.T.covering_bad_locus_criterion hX hP hGD hQ hS hK hN hX.green gram dex dg size fd deg sh) (_root_.GlobalTheory.T.covering_lambda_invariant_bound hP gram meas) size (GlobalTheory.T.covering_le_from_measure gram meas (_root_.GlobalTheory.T.covering_rationality_criterion hP)) low
end SelfIntersectionVolumeEstimates
end
