import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionTopWideIndicatorIff
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_top_wideIndicator_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  first | exact @GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | exact GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | (intros; apply GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff <;> assumption)
