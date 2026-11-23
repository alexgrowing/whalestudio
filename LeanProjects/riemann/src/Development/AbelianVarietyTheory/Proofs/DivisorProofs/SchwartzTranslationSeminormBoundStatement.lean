import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_translation_seminorm_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (a : V) (f : SchwartzMap V ℂ),
      p (SchwartzMap.compSubConstCLM ℂ (-a) f - f) ≤ ‖a‖ * (1 + ‖a‖) ^ M * q f := by
  first | exact @GlobalTheory.SchwartzTranslateLip.translate_sub_le | exact GlobalTheory.SchwartzTranslateLip.translate_sub_le | (intros; apply GlobalTheory.SchwartzTranslateLip.translate_sub_le <;> assumption)
