import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfDeepGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RefWOfSizeOfFlatDegOfRefTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceWeightOfDeepGoodStatement

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum
theorem refinedSum_weight_of_size : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → RefW :=
  fun hP _ hS hF => _root_.GlobalTheory.T.refW_of_refTheta' hP hS hF (GlobalTheory.T.reference_theta_of_core hS (GlobalTheory.T.reference_core_of_sum_point hS (GlobalTheory.T.sum_point_of_size hS)))
end GlobalTheory.RefSum
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refinedSum_weight_of_size_le : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → DeepGood → Size → FlatDeg → RefW := by
  first | exact @_root_.GlobalTheory.RefSum.refinedSum_weight_of_size | exact _root_.GlobalTheory.RefSum.refinedSum_weight_of_size | (intros; apply _root_.GlobalTheory.RefSum.refinedSum_weight_of_size <;> assumption)
end
