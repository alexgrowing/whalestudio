import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualRowsOfClassSums
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeliveryFourRowsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PRowsOfPartsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PNmjOfPDivOfClassSumPinStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem evW_pRows_of_rows_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 τ → AtAll _root_.GlobalTheory.Fc.Ind.DivisorPointSummands 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.CompatibilityConditions) 𝒜 τ → Ind.EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 τ := by
  intro hDS hHC hCR hCW 𝒜 τ hPA hDiv hG hPin
  obtain ⟨hF, hRB, -, hFr⟩ := _root_.GlobalTheory.T.fire_realBound_thR_frames_at_all hDS hHC hCR hCW 𝒜 τ
  refine Formalism.MainNotions.Closed.imp hG ?_
  intro eps Fm CH _ h hc
  obtain ⟨x0, hx0⟩ := h hc
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have ha := w3_a hc
  have hp := hPin Fm ha x hx i
  exact _root_.GlobalTheory.T.bundle_lines_of_primitive_frames_div_nmj _ _ _ _ (hF Fm ha x hx i) (hRB Fm ha x hx i) (hPA Fm ha x hx i) (hFr Fm ha x hx i)
    (hDiv Fm ha x hx i) (_root_.GlobalTheory.T.pNmj_of_pDiv_classSumPin _ _ _ _ (hDiv Fm ha x hx i) hp.1) (hx0 x hx h0 i) hp.2
end GlobalTheory.Fc.Ind
end
