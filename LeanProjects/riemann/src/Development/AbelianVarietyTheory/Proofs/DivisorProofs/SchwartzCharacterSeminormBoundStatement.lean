import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCharacterSeminormBound
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_character_seminorm_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Seminorm ℂ (SchwartzMap V ℂ)), Continuous p →
    ∃ (q : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ), Continuous q ∧ ∀ (L : V →L[ℝ] ℝ) (k : ℝ) (f : SchwartzMap V ℂ),
      p (SchwartzMap.smulLeftCLM ℂ (fun y => GlobalTheory.Published.Metaplectic.eChar (L y + k)) f - f) ≤ (‖L‖ + |k|) * (1 + ‖L‖) ^ M * q f := by
  first | exact @GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le | exact GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le | (intros; apply GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le <;> assumption)
