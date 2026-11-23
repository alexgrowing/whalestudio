import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HasExpOfLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEPartTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SidePtPartOfPackStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassSumPinOfReadAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedPart
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiesOfTiesB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtRealised
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GeoTies
set_option maxHeartbeats 1000000 in
theorem linked_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  intro hRF hL N S Γ hN hDiv
  have hE : _root_.GlobalTheory.PlugPt.HasExponent' N := (_root_.GlobalTheory.ExpTiesOfLayer.hasExp_of_layer_alt hL).2 N fun K B f T w Z Wt p0 t nch n xd c h =>
    (hN K B f T w Z Wt p0 t nch n xd c h).map Prod.fst
  let ν := _root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)
  have hRow := _root_.GlobalTheory.PlugPt.rowE_part_ties_alt hRF hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s ν (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (GlobalTheory.Plug.coreCondition_RX _ rfl)
  have hlink : ∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b → ∀ t : b.Comparison₂,
      linkOf (𝒮 := (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (fun K q c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K q c b.pt) K β c (b.part t) := by
    intro K β c b hl t
    obtain ⟨q, b', ⟨w⟩, e⟩ := hl
    have key : ∀ (x y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), x = y → ∀ t : x.2.2.Comparison₂, ∃ t' : y.2.2.Comparison₂,
        (⟨x.1, x.2.1, x.2.2.part t⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) = ⟨y.1, y.2.1, y.2.2.part t'⟩ := by
      rintro x _ rfl t
      exact ⟨t, rfl⟩
    obtain ⟨t', e'⟩ := key ⟨β.D, β.O, b⟩ _ e t
    exact ⟨q, b'.part t', _root_.GlobalTheory.T.exponent_reading_of_hasExp_bundle hL N S Γ hE K q c b' w t', e'⟩
  have hB : RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) GlobalTheory.PlugPt.RayPosition) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
      (fun _ D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) :=
    EvP.mono (fun _ K _ H β hq c b hl t => H β hq c (b.part t) (hlink K β c b hl t)) hRow
  have hR2 : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) :=
    ⟨GlobalTheory.PlugPt.RayPosition, GlobalTheory.Plug.largeBaseProperty_rayProperty hRF KPx _, RowE.row hB⟩
  obtain ⟨R, hR, hrow⟩ := RowL.and (KP := KPx) (Q := IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Q' := IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s)
    (Lk := _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) (H := AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition) hDiv hR2
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, hs⟩ := s Fm hc
  refine Built.ind (R := fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => _root_.GlobalTheory.Fc.R1.DivisorBundleCondition D O c b → (∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) → ∀ t : b.Comparison₂,
      _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) ?_ (hs x hx i).1 (H.1 Fm hc x hx i) (H.2 Fm hc x hx i)
  intro K β c b _ _ hl hdv hT
  have htw : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAll_pt β
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have key : ∀ y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, y = ⟨q.w.D q.Z, q.O, b'⟩ →
      DQ.TwAllAt y.1 y.2.1.ex.nch y.2.1.ex.xd → _root_.GlobalTheory.Fc.R1.DivisorBundleCondition y.1 y.2.1 c y.2.2 → (∀ t : y.2.2.Comparison₂,
        GlobalTheory.PlugPt.TiesB y.1 y.2.1 c (y.2.2.part t).pt ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt) →
      ∀ t : y.2.2.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands y.1 y.2.1 c (y.2.2.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (y.2.2.part t).pt ∧
        (y.2.2.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt := by
    rintro _ rfl htw hdv hT t
    obtain ⟨hTB, hRec, hMore⟩ := hT t
    have hcs := _root_.GlobalTheory.T.class_sum_divisibility_of_extensionWithLaw hL N S Γ hN K q c b' w t
    refine ⟨hcs.1, hcs.2 (_root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g _ hdv), ?_, hRec, hMore⟩
    exact _root_.GlobalTheory.PlugPt.ties_of_tiesB_alt _ _ c _ hTB hRec.1 (_root_.GlobalTheory.Fc.Ind.pt_realised_and_pb_eq _ _ c _).1 htw
  exact key ⟨β.D, β.O, b⟩ e htw hdv hT
end GlobalTheory.GeoTies
end
