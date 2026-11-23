import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FunObj.SqNum GlobalTheory.SignedHC
section Arith
variable {D : D7}
end Arith
theorem wt_tie_alt (h : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt) : _root_.GlobalTheory.BigTop.Fun.LeafWeightBound @Comparison₂ := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨0, fun CF _ => ⟨e, he, fun eps h1 h2 => ?_⟩⟩
  obtain ⟨K, hK⟩ := h eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ⟨10, fun C hC => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
  refine ⟨x0, fun x hx hle i p hp d hd => ?_⟩
  have hs := hx0 x hx hle i p hp
  obtain ⟨-, a, ha⟩ := hd
  have hw : d.Bw = (maxWt _ 1 : ℝ) := ha.sq.weight
  obtain ⟨w1, w2, hb⟩ := maxWt_le hs
  have eb : p.Z.b = (Fm.L x i).sc.b := rfl
  show 1 ≤ d.Bw ∧ d.Bw ≤ C * p.Z.b ∧ Real.log d.Bw ≤ C * Real.log p.Z.b
  rw [hw, eb]
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have l10 : Real.log 10 ≤ Real.log (Fm.L x i).sc.b := Real.log_le_log (by norm_num) (by linarith)
  have l0 : 0 ≤ Real.log (Fm.L x i).sc.b := l10.trans' (Real.log_nonneg (by norm_num))
  refine ⟨w1, w2.trans (by nlinarith), ?_⟩
  calc Real.log (maxWt _ 1 : ℝ) ≤ Real.log (10 * (Fm.L x i).sc.b) := Real.log_le_log (by linarith) w2
    _ = Real.log 10 + Real.log (Fm.L x i).sc.b := Real.log_mul (by norm_num) hb0.ne'
    _ ≤ 2 * Real.log (Fm.L x i).sc.b := by linarith
    _ ≤ C * Real.log (Fm.L x i).sc.b := by nlinarith
end GlobalTheory.BigTop.Fun
end
end
