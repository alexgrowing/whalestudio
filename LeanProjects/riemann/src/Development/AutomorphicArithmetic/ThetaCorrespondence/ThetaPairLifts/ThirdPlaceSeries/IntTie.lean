import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFittedIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
namespace GlobalTheory.BigTop.Fun.IntTie
end GlobalTheory.BigTop.Fun.IntTie
open GlobalTheory.BigTop.Fun.IntTie in
theorem GlobalTheory.BigTop.Fun.int_tie_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hd : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hB : BotSmall) (hN : BotNe) : _root_.GlobalTheory.BigTop.Fun.LeafIntegrality @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hd (gBig_dep (gBig_and hB hN))
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨h1, h2, ⟨-, -, hsmall⟩, hne⟩ := hq
  change 1 ≤ CF at h1
  change CF ≤ C at h2
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  obtain ⟨S, del, -, -, hNI, hdl⟩ := hsq.int
  obtain ⟨δ, t0, hP⟩ := hsq.norms
  choose P P' hb hz hz' using hP
  have hI := hNI δ t0 D.what₂.LL D.what₂.embLL (Sq D) P P' d.zA d.zA'
    (fun ij => hsmall δ t0 _ (P ij) (P' ij) _ ij.1 ij.2 _ (hb ij))
    (fun ij => hne δ t0 _ (P ij) (P' ij) ij.1 ij.2 (hb ij))
    (fun ij => ⟨hz ij, hz' ij⟩)
  rw [← hdl] at hI
  show NonArchimedeanDefectBound d.dl d.zA d.zA' (d.O.bDel C p.Z.b)
  refine integralNormBound_mono hI ?_
  clear hQ hne hsmall hb hz hz' hNI
  have eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := by
    have := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    norm_cast
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)
    unfold GlobalTheory.ChiGrid.sLen
    rw [hr]
    congr 3
    omega
  have eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) := hsq.weight
  have eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    rw [GlobalTheory.FunObj.SqNum.log_levQ]
    rfl
  have ef : (d.O.f : ℝ) = D.R.f := rfl
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ))) +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * Real.log p.Z.b +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) ^ 2 * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := ⟨_, rfl⟩
  have e1 : d.O.bDel C p.Z.b = C * X := by
    unfold FunData.bDel
    rw [eN, eB, eS, ef, hX]
    ring
  have e2 : GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) = CF * X := by
    unfold GlobalTheory.NormSum.intBound
    rw [hX]
    ring
  have h0 := hI.2.1 ∅
  rw [Finset.sum_empty] at h0
  change 0 ≤ GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) at h0
  change GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) ≤ _
  rw [e1, e2]
  rw [e2] at h0
  have hX0 : 0 ≤ X := (mul_nonneg_iff_of_pos_left (by linarith)).1 h0
  exact mul_le_mul_of_nonneg_right h2 hX0
end
end
