import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSquareFittedIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree
namespace GlobalTheory.BigTop.Fun.OneSqTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem lf_std_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint) : _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun _ _ d _ _ => Formalism.L2.Theta.IsStdChar _ d.W.ψ (-1) := by
  obtain ⟨CF0, h⟩ := hS.atPt big_std
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => _root_.GlobalTheory.BigTop.Fun.evPt_mono e fun x hx i p _ hq d hd => ?_⟩⟩
  obtain ⟨a, ha⟩ := hd.2
  exact hq d.G d.W d.n a ha.ok
end GlobalTheory.BigTop.Fun.OneSqTie
open GlobalTheory.BigTop.Fun.OneSqTie in
theorem GlobalTheory.BigTop.Fun.oneSq_of_log_derivative_bound_thA (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hdl : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hA : _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) (hO : OneSqSt) : _root_.GlobalTheory.BigTop.Fun.LeafUniqueSquareRoot @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hO
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and hQ (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and hA (_root_.GlobalTheory.BigTop.Fun.OneSqTie.lf_std_alt hS))) ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun ⟨hq, hth, hstd⟩ => ?_⟩
  obtain ⟨a, ha⟩ := hd.2
  have key := hq d.W a.S.toGridChoice a.rm hstd ha.ok.field CF p.R.mu d.rq d.zA d.zA' d.zT d.zTd d.gT d.ch d.N0 d.Sd d.Se
    d.dl d.Bw hth ha.sq
  have e1 : (p.S false).μ = p.R.mu := rfl
  have e2 : p.P.A3.fam3.base3.μ0 = p.P.A3.A.μ0 := rfl
  have hsq := ha.sq
  have hm : d.O.m = D.R.m := rfl
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hkm := D.R.m_add_three_le_k
  obtain ⟨ka, hka⟩ := D.R.k_even
  obtain ⟨mb, hmb⟩ := D.R.m_even
  obtain ⟨tc, htc⟩ := D.R.t_odd
  have hs : GlobalTheory.ChiGrid.sLen D = D.R.k + D.R.m + 5 := by unfold GlobalTheory.ChiGrid.sLen; rw [hr]; omega
  have E : ∀ ij : Sq D, sqRank D ij =
      2 * (D.R.r + (ij.2 : ℕ) * D.R.t + (ij.1 : ℕ) * GlobalTheory.ChiGrid.sLen D) + (D.R.t + GlobalTheory.ChiGrid.sLen D) := by
    intro ij; unfold sqRank GlobalTheory.ChiGrid.rankV; ring
  have E' : ∀ ij : Sq D, GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = d.O.hd ij := by
    intro ij
    show (GlobalTheory.ChiGrid.rankV D ((ij.1 : ℕ) + 1) ((ij.2 : ℕ) + 1) + GlobalTheory.ChiGrid.rankV D ij.1 ij.2) / 2 = sqRank D ij / 2
    congr 1
    unfold sqRank GlobalTheory.ChiGrid.rankV; ring
  have hev : ∀ ij : Sq D, sqRank D ij = 2 * (sqRank D ij / 2) := by
    intro ij
    rw [E ij, hs]
    omega
  have hN : d.O.N = D.R.k + D.R.m * D.R.t + D.R.m * GlobalTheory.ChiGrid.sLen D + D.R.m := by
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = _
    rw [hs]; ring
  refine ⟨fun ij => hsq.rq_base ij, fun w ij => (key w ij).1, fun l hl => ((hsq.err l).1 hl).1, fun ij => hev ij,
    fun ij => ?_, fun ij => ?_, fun q _ => ?_, fun w ij => ?_⟩
  · show sqRank D ij ≤ 2 * d.O.N
    rw [hN, E ij]
    have h1 : (ij.2 : ℕ) * D.R.t + D.R.t ≤ D.R.m * D.R.t := by
      calc (ij.2 : ℕ) * D.R.t + D.R.t = ((ij.2 : ℕ) + 1) * D.R.t := by ring
        _ ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ (by omega)
    have h2 : (ij.1 : ℕ) * GlobalTheory.ChiGrid.sLen D + GlobalTheory.ChiGrid.sLen D ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := by
      calc (ij.1 : ℕ) * GlobalTheory.ChiGrid.sLen D + GlobalTheory.ChiGrid.sLen D = ((ij.1 : ℕ) + 1) * GlobalTheory.ChiGrid.sLen D := by ring
        _ ≤ D.R.m * GlobalTheory.ChiGrid.sLen D := Nat.mul_le_mul_right _ (by omega)
    rw [hr]
    omega
  · show D.R.m - 1 - (ij.2 : ℕ) + 1 ≤ D.R.m
    omega
  · classical
    show (if q = d.G.pl.v0 then 1 else 2) ≤ (if q = d.G.pl.v0 then _ else 2)
    split_ifs <;> omega
  · have h := (key w ij).2
    have hd2 : 2 * GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = d.O.dd ij := by
      rw [E' ij]; exact (hev ij).symm
    rw [hd2, E' ij] at h
    exact h
end
end
