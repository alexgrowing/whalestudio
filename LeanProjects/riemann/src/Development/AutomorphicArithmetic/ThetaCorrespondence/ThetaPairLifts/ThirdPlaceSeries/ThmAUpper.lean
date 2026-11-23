import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFamilyEstimate
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QnNotMemStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValBoundTwistedStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
noncomputable section
namespace GlobalTheory.ThmAUpper
theorem thmA_upper_alt : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint →
    (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx →
    (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  intro hG hS hdl hF hT
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hF) (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hT)) ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH hp hd
  refine ⟨hd, fun ⟨hf, ht⟩ w hw => ⟨_root_.GlobalTheory.T.qn_not_mem_asIdeal_of_mu_ne p CF d hp hd w hw, fun l hl hlw i j s Λ Λd z hs1 hs2 hΛ hΛd hz => ?_⟩⟩
  have hw' : D.plEq (D.plEq.symm w) = w := D.plEq.apply_symm_apply w
  have hl' : D.what₂.places.resChar (D.plEq.symm w) = l := resChar_eq _ hl (by rw [hw']; exact hlw)
  have key := _root_.GlobalTheory.T.cm_abelian_field_data_of_toric_ratio_alt p CF d hp hd hG hf ht (D.plEq.symm w) (xiH_twisted p w hw).1 i j s Λ Λd z hs1 hs2
    (by rw [← nuH_twisted p d.G w hw]; exact hΛ) (by rw [hl']; exact hΛd) hz
  rw [hw', hl'] at key
  exact key
end GlobalTheory.ThmAUpper
end
end
