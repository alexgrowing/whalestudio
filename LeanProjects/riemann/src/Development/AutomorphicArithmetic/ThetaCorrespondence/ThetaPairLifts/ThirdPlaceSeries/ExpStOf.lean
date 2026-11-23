import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ExpTie.Asm
open Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
end Point
theorem expSt_of_alt : Formalism.CohomologicalDescent.E.ExCut → _root_.GlobalTheory.ExpTie.NumStAlt → _root_.GlobalTheory.ExpTie.ExponentSumStatement → _root_.GlobalTheory.ExpTie.ModelStatement → _root_.GlobalTheory.BigOn.ExponentStatement := by
  intro hcut hN hS hM
  obtain ⟨a, ha, H⟩ := (hN.and hS).and hM
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, N1⟩, ⟨x2, S1⟩⟩, ⟨x3, M1⟩⟩ := hK Fm CH hc hL
  refine ⟨0, fun c _ _ => ⟨max x1 (max x2 x3), fun x hx hle i p hp hMo r O hR => ?_⟩⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  choose Pj Wj hPW using N1 x hx h1 i p hp hMo
  obtain ⟨st, hRT⟩ := hR.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  intro C CH'
  exact hasExpBound_at p hcut O hRT.m_eq hRT.x_eq hRT.eps_eq hR.1.realisedChain_torus_eq Pj Wj (fun j => (hPW j).1) (fun j => (hPW j).2)
    (fun j t w => S1 x hx h2 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 t w)
    (fun j w hw hR' => M1 x hx h3 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 w hw hR') C CH'
end GlobalTheory.ExpTie.Asm
end
end
