import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.NormalizedCovolumeEqOne
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CovolumeLowerBoundOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureBoundStatementStatement

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
namespace GlobalTheory.CovTop.MeasRd
theorem covering_measure_reduction : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Meas := by
  intro h
  have h2 := _root_.GlobalTheory.T.normalized_covolume_eq_one h
  refine Closed.imp (Closed.and (GlobalTheory.T.log_ratio_upper_bound h2) (_root_.GlobalTheory.T.covolume_lower_bound_of_cover h)) ?_
  intro _ Fm _ _ hh
  obtain ⟨⟨K1, hK1, a, ha⟩, ⟨K2, hK2, b, hb⟩⟩ := hh
  refine ⟨(K1 + K2) / 2, by positivity, max a b, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨hr, hu⟩ := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hl := hb x hx ((le_max_right _ _).trans hle) ι p hp i
  exact measAt_of p i (GlobalTheory.T.exact_at_of_one_measure p hp.1 (h2 _) i) hr hK1 hK2 hu hl
end GlobalTheory.CovTop.MeasRd
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_measure_reduction_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Meas := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction | exact _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction <;> assumption)
end
