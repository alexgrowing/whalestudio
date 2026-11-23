import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedStateTransportHeqLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewTwistLamFullStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SeriesStep
open GlobalTheory.Mem.R3.Tr
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem listPin_oTw (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (c b : ℝ) {I : Type}
    (Lc : Formalism.IndefR.Links.LevCh (Dof x) I) (h : ListPin (Dof x) Lc c b) :
    ListPin (w.st (oTw x N).Z).toD7 (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z Lc) c b := by
  obtain ⟨G, h1, h2⟩ := h
  exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oTw x N).Z G) :)), ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩, (by with_unfolding_all exact ((hN _ h2) :))⟩

theorem listSt_oTw (cDep : ℝ) (x : St P) (N : TwNew (Dof x))
    (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof x), GlobalTheory.LamTie.IsLamTieFull (Dof x).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
    (x' : St P) (ho : x'.o = oTw x N)
    (hR : HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh))
    (h : ListSt cDep x) : ListSt cDep x' := by
  unfold ListSt
  generalize x'.m.z.R.toRealDat.toLevCh = Lc' at hR ⊢
  revert Lc'
  unfold Dof
  rw [ho]
  intro Lc' hR
  rw [eq_of_heq hR]
  exact listPin_oTw x N hN _ _ _ h

theorem sb1l : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, SeriesExistList hL cDep := by
  intro hPr hSer hL cDep
  refine (StepW.and (GlobalTheory.MtId.inMt_idFrame hPr) (StepW.of_all fun _ _ _ _ _ _ _ h => h)).trans
    (StepW.of_all fun K B f T w hK hF H P x l => ?_)
  obtain ⟨N, hN, hser⟩ := GlobalTheory.T.exists_new_twist_lam_full hPr hSer hL hK hF H.2 x l
  obtain ⟨x', l', ho, hLc, hrow, hPq, hS, hSb, hhL, heig, hθ, hR, hcG, hgeo⟩ := GlobalTheory.T.twisted_state_transport_heq_levels hL x l.toLI N
  obtain ⟨m, hm⟩ := H.1 P x'
  obtain ⟨b⟩ := hser x' l' ho hrow hPq hS hSb hhL heig hθ hR hcG hgeo m hm
  exact ⟨x', ⟨{ toLI := { l' with mt := m }, b := b }⟩, listSt_oTw cDep x N hN x' ho hLc⟩

end GlobalTheory.HeightCounting.Up.SeriesStep
