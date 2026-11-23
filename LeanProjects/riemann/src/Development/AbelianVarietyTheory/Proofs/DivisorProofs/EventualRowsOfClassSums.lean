import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationInputsAllPartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPartOfClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfAllPartPropertiesStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.Ind

theorem evW_pRows_of_rows : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel Ind.Part 𝒜), AtAll Ind.PPA 𝒜 τ → AtAll Ind.PDiv 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : Ind.Part D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.Ties) 𝒜 τ → Ind.EvW Ind.PRows 𝒜 τ := by
  intro hDS hHC hCR hCW 𝒜 τ hPA hDiv hG hPin
  obtain ⟨hF, hRB, -, hFr⟩ := GlobalTheory.T.representation_inputs_all_parts hDS hHC hCR hCW 𝒜 τ
  refine Formalism.MainNotions.Closed.imp hG ?_
  intro eps Fm CH _ h hc
  obtain ⟨x0, hx0⟩ := h hc
  refine ⟨x0, fun x hx h0 i => ?_⟩
  have ha := w3_a hc
  have hp := hPin Fm ha x hx i
  exact GlobalTheory.T.rows_of_all_part_properties _ _ _ _ (hF Fm ha x hx i) (hRB Fm ha x hx i) (hPA Fm ha x hx i) (hFr Fm ha x hx i)
    (hDiv Fm ha x hx i) (GlobalTheory.T.normalized_part_of_class_sum _ _ _ _ (hDiv Fm ha x hx i) hp.1) (hx0 x hx h0 i) hp.2

end GlobalTheory.Fc.Ind
