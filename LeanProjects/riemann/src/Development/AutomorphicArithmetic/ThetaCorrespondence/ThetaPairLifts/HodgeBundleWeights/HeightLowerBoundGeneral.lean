import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.NefModelVolumes.HeightG
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightAddLogNonneg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsShortSectionCoverHeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeometricOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RefinedSumWeightOfSizeLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsSectionBoundedByBergmanKernel

section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates
set_option maxHeartbeats 1000000 in
theorem height_lower_bound_general : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → DeepGood → Size → Deg → FlatDeg → Height :=
  fun hSB hX hGD hQ hP hH hD hG hS hDg hF => _root_.GlobalTheory.CovHt.HtTopG.height_of_geom_multC_budget_meanAll hSB hP hG hS hDg (_root_.GlobalTheory.T.exists_short_section_cover_height hP hG hS hF) (_root_.GlobalTheory.T.geom_of_published_inputs hX hGD hQ hP hH.sieg hX.ks hX.lie hG hS) (GlobalTheory.T.carrying_section_integral_frame (_root_.GlobalTheory.T.refinedSum_weight_of_size_le hP hG hS hF) (_root_.GlobalTheory.T.exists_section_bounded_by_bergman_kernel hP hH hG hS hF)) (GlobalTheory.T.budget_of_size_and_weight GlobalTheory.T.host_bound_holds GlobalTheory.T.weight_bound_holds hS) hD
end SelfIntersectionVolumeEstimates
end
