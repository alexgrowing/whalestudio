import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerTranslationSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
open scoped SchwartzMap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_translation_seminorm_bound : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : V → V → ℝ), GlobalTheory.ArchUniq.IsPairing P → ∀ (s₀ : Finset (ℕ × ℕ)), ∃ (M : ℕ) (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (w : V × V) (h : 𝓢(V, ℂ)), ∃ g : 𝓢(V, ℂ), ⇑g = GlobalTheory.ArchUniq.schrF P w ⇑h ∧ (s₀.sup (schwartzSeminormFamily ℂ V ℂ)) g ≤ C * (1 + ‖w‖) ^ M * (s.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
  first | exact @GlobalTheory.SchrGrowth.schrF_seminorm_growth | exact GlobalTheory.SchrGrowth.schrF_seminorm_growth | (intros; apply GlobalTheory.SchrGrowth.schrF_seminorm_growth <;> assumption)
