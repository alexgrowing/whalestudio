import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundleStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasExpOfLayer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RowEPartTies
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TiesOfTiesB
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LargeBaseRayCondition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreSlotRX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtRealised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoTies

theorem twAllAt_tr {D : D7} (N : ∀ u, Submodule (NumberField.RingOfIntegers D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    {x : NChoice D} {y : ThData D} (H : DQ.TwAllAt D x y) : DQ.TwAllAt (setDiv D N h) (nchTr N h x) (xdTr N h y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, fun a ha => ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2 a ha
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr N h _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

theorem twAll_pt {K : Ctx} (β : BPt K) : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAllAt_tr (nPrime β.p.L) β.p.ht β.twAll

set_option maxHeartbeats 1000000 in

theorem linked_ties : GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) R1.DivisorConditionAtBundlePoints → RL.At (prmR N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : Bundle D O c) => ∀ t : b.Comparison₂, Ind.PIota D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.Ties ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  intro hRF hL N S Γ hN hDiv
  have hE : GlobalTheory.PlugPt.HasExp N := (GlobalTheory.ExpTiesOfLayer.hasExp_of_layer hL).2 N fun K B f T w Z Wt p0 t nch n xd c h =>
    (hN K B f T w Z Wt p0 t nch n xd c h).map Prod.fst
  let ν := GlobalTheory.PlugPt.NRead.of RX hE (SXE S) (OX Γ)
  have hRow := GlobalTheory.PlugPt.rowE_part_ties hRF hL (prmR N S Γ).s ν (IsGoodE (prmR N S Γ).s) (GlobalTheory.Plug.coreCondition_RX _ rfl)
  have hlink : ∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : Bundle β.D β.O c), IsLinked (prmR N S Γ) K β c b → ∀ t : b.Comparison₂,
      linkOf (𝒮 := (prmR N S Γ).s) (Bd := Ind.Part) (fun K q c b => GlobalTheory.PlugPt.pinPt ν K q c b.pt) K β c (b.part t) := by
    intro K β c b hl t
    obtain ⟨q, b', ⟨w⟩, e⟩ := hl
    have key : ∀ (x y : Σ (D : D7) (O : Obj D), Bundle D O c), x = y → ∀ t : x.2.2.Comparison₂, ∃ t' : y.2.2.Comparison₂,
        (⟨x.1, x.2.1, x.2.2.part t⟩ : Σ (D : D7) (O : Obj D), Ind.Part D O c) = ⟨y.1, y.2.1, y.2.2.part t'⟩ := by
      rintro x _ rfl t
      exact ⟨t, rfl⟩
    obtain ⟨t', e'⟩ := key ⟨β.D, β.O, b⟩ _ e t
    exact ⟨q, b'.part t', GlobalTheory.T.exponent_reading_bundle hL N S Γ hE K q c b' w t', e'⟩
  have hB : RowE (sAnd (IsGoodE (prmR N S Γ).s) GlobalTheory.PlugPt.RayPosition) (IsLinked (prmR N S Γ))
      (fun _ D O c (b : Bundle D O c) => ∀ t : b.Comparison₂, GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) :=
    EvP.mono (fun _ K _ H β hq c b hl t => H β hq c (b.part t) (hlink K β c b hl t)) hRow
  have hR2 : RL.At (prmR N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : Bundle D O c) => ∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) :=
    ⟨GlobalTheory.PlugPt.RayPosition, GlobalTheory.Plug.largeBaseProperty_rayProperty hRF KPx _, RowE.row hB⟩
  obtain ⟨R, hR, hrow⟩ := RowL.and (KP := KPx) (Q := IsBuiltE (prmR N S Γ).s) (Q' := IsGoodE (prmR N S Γ).s)
    (Lk := IsLinked (prmR N S Γ)) (H := AtAll R1.P_hDivG) hDiv hR2
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, hs⟩ := s Fm hc
  refine Built.ind (R := fun D O c (b : Bundle D O c) => R1.P_hDivG D O c b → (∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) → ∀ t : b.Comparison₂,
      Ind.PIota D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.Ties ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) ?_ (hs x hx i).1 (H.1 Fm hc x hx i) (H.2 Fm hc x hx i)
  intro K β c b _ _ hl hdv hT
  have htw : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAll_pt β
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have key : ∀ y : Σ (D : D7) (O : Obj D), Bundle D O c, y = ⟨q.w.D q.Z, q.O, b'⟩ →
      DQ.TwAllAt y.1 y.2.1.ex.nch y.2.1.ex.xd → R1.P_hDivG y.1 y.2.1 c y.2.2 → (∀ t : y.2.2.Comparison₂,
        GlobalTheory.PlugPt.TiesB y.1 y.2.1 c (y.2.2.part t).pt ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt) →
      ∀ t : y.2.2.Comparison₂, Ind.PIota y.1 y.2.1 c (y.2.2.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (y.2.2.part t).pt ∧
        (y.2.2.part t).pt.Ties ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt := by
    rintro _ rfl htw hdv hT t
    obtain ⟨hTB, hRec, hMore⟩ := hT t
    have hcs := GlobalTheory.T.class_sum_divisibility_bundle hL N S Γ hN K q c b' w t
    refine ⟨hcs.1, hcs.2 (FourBoundsAtBundles.pDiv_of _ hdv), ?_, hRec, hMore⟩
    exact GlobalTheory.PlugPt.ties_of_tiesB _ _ c _ hTB hRec.1 (Ind.pt_ties0 _ _ c _).1 htw
  exact key ⟨β.D, β.O, b⟩ e htw hdv hT

end GlobalTheory.GeoTies
