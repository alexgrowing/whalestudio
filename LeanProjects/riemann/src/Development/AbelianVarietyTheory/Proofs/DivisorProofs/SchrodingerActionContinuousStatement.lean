import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerActionContinuous
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_action_continuous : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (f : 𝓢(V, ℂ)), Continuous fun w : V × V => GlobalTheory.SchrPairing.schrSch hP w f := by
  first | exact @GlobalTheory.SchrPairing.continuous_schrSch | exact GlobalTheory.SchrPairing.continuous_schrSch | (intros; apply GlobalTheory.SchrPairing.continuous_schrSch <;> assumption)
