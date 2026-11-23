import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImply
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement

section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop
theorem PublishedHodgeBundleTheorems.toClassicalTheorems : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := fun h => h.toClassicalTheoremsOf GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil
end GlobalTheory.CovTop
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_topology_refinement : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.Hypotheses'' := by
  first | exact @_root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | exact _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems | (intros; apply _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems.toClassicalTheorems <;> assumption)
end
