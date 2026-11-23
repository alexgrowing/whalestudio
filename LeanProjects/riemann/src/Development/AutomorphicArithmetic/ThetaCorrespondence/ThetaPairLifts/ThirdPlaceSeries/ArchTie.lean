import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanFittedIdentity
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
theorem GlobalTheory.BigTop.Fun.arch_tie_of_logDeriv_bound (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hd : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (_hA : GlobalTheory.NormSum.ArchSt) (_hB : BotSmall) : _root_.GlobalTheory.BigTop.Fun.ArchimedeanCondition @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hd GlobalTheory.T.archimedeanBound_bottomPairs_norms_grid
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  have hA := hq d.zA d.zA' hsq.norms
  show ArchimedeanHeightBound d.zA d.zA' (d.O.bArch C p.Z.b)
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
  have e1 : d.O.bArch C p.Z.b = C * D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        (Real.log p.Z.b + Real.log ((GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)))) +
      C * D.R.f * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 *
        (Real.log p.Z.b + Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ))) +
      C * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 2 * Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    unfold FunData.bArch
    rw [eN, eB, eS, ef]
  rw [e1]
  exact hA
end
end
