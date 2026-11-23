import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFderivParametricUniformBound
import Mathlib
open Set
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iterated_fderiv_parametric_uniform_bound : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set (ℝ × E)} {Φ : ℝ × E → F} {A : Set ℝ} {K : Set E}, IsOpen S → ContDiffOn ℝ ∞ Φ S → IsCompact A → IsCompact K → A ×ˢ K ⊆ S → ∀ k : ℕ, ∃ M : ℝ, ∀ ε ∈ A, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (fun y => Φ (ε, y)) x‖ ≤ M := by
  first | exact @GlobalTheory.exists_bound_iteratedFDeriv_snd_of_isCompact_prod | exact GlobalTheory.exists_bound_iteratedFDeriv_snd_of_isCompact_prod | (intros; apply GlobalTheory.exists_bound_iteratedFDeriv_snd_of_isCompact_prod <;> assumption)
