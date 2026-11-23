import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffBoundStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffBoundStatementStatement

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem covering_cut_of_local_traces (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : Cut := by
  refine (Sizes.hostN 3).imp fun Fm CH _ h => ?_
  obtain ⟨C, -, x0, hx⟩ := h
  exact ⟨0, le_rfl, x0, fun x hx' hle ι p hp i => cutAt_of_rows p hp.1 hp.2 i _ _ (hx x hx' hle ι p hp i)⟩
end GlobalTheory.CovTop
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_cut_criterion : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Cut := by
  first | exact @_root_.GlobalTheory.CovTop.covering_cut_of_local_traces | exact _root_.GlobalTheory.CovTop.covering_cut_of_local_traces | (intros; apply _root_.GlobalTheory.CovTop.covering_cut_of_local_traces <;> assumption)
end
