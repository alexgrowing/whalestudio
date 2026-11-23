import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoreSlotConstructionMonoFewerCoresBothPasses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.HeightCounting.Up
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem builtE_of_nExt_alt {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (c : V4.Core K (w.st Z) f T)
    (h : BuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K B f T w Z c) : BuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K B f T w Z c := by
  obtain ⟨b, hb⟩ := h
  exact ⟨{ b with nx := ⟨b.nx.1, Classical.choice (hN _ _ _ _ _ _ _ _ _ _ _ _ _ b.nx.2)⟩ }, hb⟩
noncomputable def witnessOfExtensionImplication {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {O : Obj2 (w.D Z)}
    (x : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K w Z O) : Wit (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K w Z O :=
  { x with nx := ⟨x.nx.1, Classical.choice (hN _ _ _ _ _ _ _ _ _ _ _ _ _ x.nx.2)⟩ }
noncomputable def weightedPointOfExtensionImplication {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    {K : Ctx} (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K) : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K :=
  ⟨q.B, q.f, q.T, q.w, q.Z, q.O, _root_.GlobalTheory.HeightCounting.Up.witnessOfExtensionImplication hN q.x⟩
theorem nonempty_bWit_wptOfNExt {N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL} {S : SExt} {Γ : GeoP}
    (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c))
    {K : Ctx} (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (h : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness (_root_.GlobalTheory.HeightCounting.Up.weightedPointOfExtensionImplication hN q) b) := by
  have r := h.recPin
  exact ⟨⟨h.x, h.a, h.ax, h.y,
    { s := ⟨r.s.host, r.s.cols, r.s.full, r.s.g, r.s.theta, r.s.twE, r.s.twGood, r.s.chr, r.s.gal, r.s.nn, r.s.exp, r.s.chiD,
        r.s.twF, r.s.types, r.s.cover, r.s.plB, r.s.thetaChr, r.s.dt, r.s.pieces, r.s.inK, r.s.geo, r.s.tw⟩
      k := ⟨r.k.std, r.k.O, r.k.ent, r.k.adapted, r.k.top⟩
      crd := r.crd, entC := r.entC, std := r.std, rd := r.rd },
    h.s, h.pt, h.sx, h.eF, h.fi, h.uS, h.parts, h.cW, h.d3b, h.side, h.colPins⟩⟩
end GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem rows_of_stronger_nExt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c)) → (∀ K X f T c, IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c) ∧ (∀ K X f T c, IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c) ∧ (∀ K β c b, _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) K β c b → _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b) ∧ ∀ (M : FamClass → Prop) (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType), _root_.GlobalTheory.Fc.AllRowsAlt KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) M DR → _root_.GlobalTheory.Fc.AllRowsAlt KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ)) M DR := by
  intro hL N N' S Γ hN
  have hB : ∀ K X f T c, IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c :=
    positionOf_mono (_root_.GlobalTheory.HeightCounting.Up.builtE_of_nExt_alt hN)
  have hG : ∀ K X f T c, IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ).s K X f T c → IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K X f T c :=
    positionOf_mono fun K B f T w Z c h => ⟨_root_.GlobalTheory.HeightCounting.Up.builtE_of_nExt_alt hN K B f T w Z c h.1, h.2⟩
  have hLk : ∀ K β c b, _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) K β c b → _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b := by
    rintro K β c b ⟨q, b', ⟨h⟩, e⟩
    exact ⟨_root_.GlobalTheory.HeightCounting.Up.weightedPointOfExtensionImplication hN q, b', _root_.GlobalTheory.HeightCounting.Up.nonempty_bWit_wptOfNExt hN q b' h, e⟩
  refine ⟨hB, hG, hLk, fun M DR A => ?_⟩
  exact {
    hn4 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hn4
    jOn := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.jOn
    hInstR := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hInstR
    aC2 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aC2
    aP10 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aP10
    aAtG := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aAtG
    aPt0 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPt0
    aPtTw := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPtTw
    aPer0 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPer0
    aPerTw := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.aPerTw
    tie := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.tie
    hRB := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hRB
    hTw := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hTw
    hPA := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hPA
    hLamP := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hLamP
    hDivG := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hDivG
    hDcPtG := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hDcPtG
    selJ := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.selJ
    sLp := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.sLp
    sO := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.sO
    hServ := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hServ
    zL := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.zL
    hTF := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.hTF
    rRows := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.rRows
    nRest := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => row_mono_id hS hLk h) A.nRest
    c30 := eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => let ⟨c, cI, h1, h2, h3⟩ := h; ⟨c, cI, h1, h2, row_mono_id hS hLk h3⟩) A.c30 }
end GlobalTheory.HeightCounting.Up
end
