import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventualRowsOfClassSums
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventual_rows_of_class_sums : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (τ : RawSel Ind.Part 𝒜), AtAll Ind.PPA 𝒜 τ → AtAll Ind.PDiv 𝒜 τ → Ind.EvW (fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D) 𝒜 τ → AtAll (fun D O c (b : Ind.Part D O c) => GlobalTheory.ExportPin.ClassSumPin b.pt ∧ b.pt.Ties) 𝒜 τ → Ind.EvW Ind.PRows 𝒜 τ := by
  first | exact @GlobalTheory.Fc.Ind.evW_pRows_of_rows | exact GlobalTheory.Fc.Ind.evW_pRows_of_rows | (intros; apply GlobalTheory.Fc.Ind.evW_pRows_of_rows <;> assumption)
