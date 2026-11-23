import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBoundFittedIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
namespace GlobalTheory.BigTop.Fun.ThbTie
end GlobalTheory.BigTop.Fun.ThbTie
open GlobalTheory.BigTop.Fun.ThbTie in
theorem GlobalTheory.BigTop.Fun.thb_tie_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hd : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hT : ThbSt) : _root_.GlobalTheory.BigTop.Fun.LeafThetaBound @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hd hT
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono hQ ?_
  intro D L hT' Gi Gl Kc Y cX ex Csz p CF d C CH _ htie
  refine ⟨htie, fun hq => ?_⟩
  obtain ⟨a, ha⟩ := htie.2
  have hsq := ha.sq
  have hin : ∀ (ij : Sq D) (s : ℤ), 1 ≤ s → s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 →
      Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 (bTH D C p.Z.x p.Z.b) ∧
        ∀ c, d.zTd ij c s ≠ 0 ∧ Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) (bTH D C p.Z.x p.Z.b) := by
    intro ij s h1 h2
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ s)
    have h1' : 1 ≤ n := by omega
    have h2' : n ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by omega
    exact hq ij.1 ij.2 n h1' h2' _ _ (hsq.inside ij n h1' h2').1
  have hB0 : ∀ ij : Sq D, 0 ≤ bTH D C p.Z.x p.Z.b := by
    intro ij
    have hr : 1 ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
      have := D.R.m_add_three_le_k
      unfold GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
      have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
      omega
    exact htLe_nonneg (hin ij 1 le_rfl (by exact_mod_cast hr)).1
  have hB : d.O.bTH C p.Z.x p.Z.b = bTH D C p.Z.x p.Z.b := rfl
  have hzT : ∀ ij s, d.O.zT ij s = 1 := hsq.base
  refine ⟨fun ij s h1 h2 => ?_, fun ij s => ?_, fun ij c s => ?_⟩
  · have h2' : s ≤ (GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 : ℤ) :=
      h2.trans_eq (congrArg (fun n : ℕ => (n : ℤ)) (sqRank_half (D := D) ij))
    exact ⟨by rw [hzT]; exact one_ne_zero, fun c => ((hin ij s h1 h2').2 c).1⟩
  · rw [hzT, hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact (hin ij s hs.1 hs.2).1
    · have := (hsq.outside ij s hs).2.1
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) 1 _
      rw [this]
      exact htLe_one_zero (hB0 ij)
  · rw [hB]
    by_cases hs : 1 ≤ s ∧ s ≤ GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2
    · exact ((hin ij s hs.1 hs.2).2 c).2
    · obtain ⟨e1, e2, -⟩ := hsq.outside ij s hs
      change Formalism.PairingDivisionLocalBalance.HtLe (d.gT ij s) (d.zTd ij c s) _
      rw [e1 c, e2]
      exact htLe_one_zero (hB0 ij)
end
end
