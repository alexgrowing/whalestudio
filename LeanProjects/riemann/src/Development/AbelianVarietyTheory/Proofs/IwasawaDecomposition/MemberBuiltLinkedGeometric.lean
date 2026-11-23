import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricParameterUniformStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphyOfPublishedInputsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PublishedInputsImplyConclusionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SlotStageMovesGeometricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendsFineAdelicDatumLargerFieldOfPublishedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsFromPrintedInputsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllReductionStatementsHoldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteLevelAndSecondStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Top.Bl

theorem has3_neo_of_localLanglands (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (hB : ExistsUnlocalizedSaturatedState) (hA : SA hL) (hMt : SMt) (hRat : SRat hL)
    (hCu : SCusp hL) (hB0 : SettingsFormsExistList hL cDep) (hB1 : SeriesExistList hL cDep) (hB2 : ModuliPointsExistList hL cDep) (hC : SC hL) (hFin : SFino hL cDep)
    (S : SExt) (Γ : GeoP) : StepW Start (Has3 (prmR (NEo hL cDep) S Γ).s) := by
  have h := StepW.and hB (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
  refine h.trans (StepW.of_all ?_)
  intro K B f T w _ _ H
  obtain ⟨⟨P, x, sat, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
  obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
  obtain ⟨imt⟩ := mt P x1
  obtain ⟨irat⟩ := rat P x1 la
  have li : LI hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
  obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
  obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
  obtain ⟨sc⟩ := c P x4 l2
  obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ ⟨p4 (p3 p2), sat⟩
  exact ⟨Z, ⟨v⟩⟩

theorem memberE_exBL_of_pair (hA : HypA) (hE : HypE) (hH : HypH) (hL : GlobalTheory.Published.LocalLanglandsGL) (hN : HypN hL) (N Ng : NExt hL)
    (toB : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c))
    (toN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd)
    (has3 : StepW Start (Has3 (prmR N SExt.none (geoCl anyGeometry)).s))
    (lv : LevelThreeCondition (prmR N SExt.none (geoCl anyGeometry)).s) (lvg : LevelThreeCondition (prmR Ng SExt.none (geoCl anyGeometry)).s)
    (intersection_update_fsHerm_neg_one : PositionMv (prmR N SExt.none (geoCl anyGeometry)).s)
    (second : Pass KPx (IsBuiltE (prmR N SExt.none (geoCl anyGeometry)).s) fun K B f T =>
      ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR Ng SExt.none (geoCl anyGeometry)).s K B f T w)
    (hMQ : MultQ (prmR N SExt.none (geoCl anyGeometry))) :
    MemberE (prmR N SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (prmR N SExt.none (geoCl anyGeometry)).s) (IsGoodE (prmR N SExt.none (geoCl anyGeometry)).s)
        (IsLinked (prmR N SExt.none (geoCl anyGeometry))) := by
  have exp := GlobalTheory.T.automorphy_of_hypotheses hE.e1 hE.e2 hE.e3 hE.e4 hE.e5 hE.e6 hE.e7 hE.e8 hE.e9 hE.e10 hE.e11 hE.e12 hE.e13 hA.a6 hE.e14 hA.a22
    hE.e15 hE.e16 hE.e17 hE.e18 hE.e19 hE.e20 hE.e21 hE.e22 hE.e23 hE.e24 hE.e25 hN.pr hN.ser hL hN.parMem N
    SExt.none (geoCl anyGeometry) toB
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.T.published_inputs_imply_conclusion hA.a1 hA.a2 hA.a3 hA.a11 hA.a10 hA.a6 hA.a12 hA.a13 hA.a14 hA.a15 hA.a16 hA.a17 hA.a18 hA.a8 hA.a6 hA.a7
      hA.a5 hA.a19 hA.a20 hA.a21 hL N Ng has3 lv lvg exp second toN
  · exact GlobalTheory.T.geometric_parameter_uniform hH.h1.q12 hH.cover hA.a5 hA.a7 hA.a8 hA.a9 hA.a10 hA.a6 hA.a22 hA.a23 hA.a1 hL N (geoCl anyGeometry)
      (prmR N SExt.none (geoCl anyGeometry)) rfl toB intersection_update_fsHerm_neg_one hMQ

theorem memberE_exBL_prm1 : HypA → HypE → HypH → ExistsUnlocalizedSaturatedState → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, HypN hL → ∀ cDep : ℝ,
    MultQ (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)).s)
        (IsGoodE (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry)).s) (IsLinked (prmR (NEo hL cDep) SExt.none (geoCl anyGeometry))) := by
  intro hA hE hH hW hL hN cDep hMQ
  have holdsW : WeightCaseCondition := GlobalTheory.T.weight_set_residue_characteristic hH.h1 hH.h2 hH.h3 hH.multW
  have datE : DatExt := GlobalTheory.T.fineAdelicDatum_extends_to_larger_field_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  have h := GlobalTheory.T.all_reduction_statements_hold (by first | exact hA.a5 | exact hA.a7) (by first | exact hA.a5 | exact hA.a7)
  repeat (first | specialize h hA.a8 | specialize h hA.a9 | specialize h hA.a12 | specialize h hA.a5 | specialize h hA.a6 | specialize h hA.a7 | specialize h hA.a10 | specialize h hA.a22 | specialize h hH | specialize h hN.pr | specialize h hN.ser | specialize h hL | specialize h hN.arch | specialize h hN.pt)
  obtain ⟨sA, sMt, sRat, sCusp, -, -, -, sC, -, sl⟩ := h
  obtain ⟨fin, second⟩ := GlobalTheory.T.finite_level_and_second hH.cover (by first | exact hA.a5 | exact hA.a7) (by first | exact hA.a5 | exact hA.a7) hN.pr hN.ser datE holdsW hA.a9 hN.arch.pht hL sMt sRat sCusp cDep (sl cDep).2.2.2
  have has3 := has3_neo_of_localLanglands hL cDep hW sA sMt sRat sCusp (sl cDep).1 (sl cDep).2.1 (sl cDep).2.2.1 sC fin SExt.none (geoCl anyGeometry)
  have lv := GlobalTheory.T.lv3Mv_prmR_NEo_and_NEog hL cDep SExt.none (geoCl anyGeometry)
  exact memberE_exBL_of_pair hA hE hH hL hN (NEo hL cDep) (NEog hL cDep) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨⟨h.1⟩, h.2.down⟩) has3 lv.1 lv.2 (GlobalTheory.T.movable_geometric hL cDep anyGeometry)
    (second SExt.none (geoCl anyGeometry)) hMQ

end GlobalTheory.Mem.Top.Bl
