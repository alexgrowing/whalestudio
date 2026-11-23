import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeOfExpanding
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_le_pow_mul_setIntegral_of_expanding : ∀ (N : ℕ) (A Q : Set (Fin N → ℝ)) (K : ℝ) (f : (Fin N → ℝ) → (Fin N → ℝ)) (h₁ h₂ : (Fin N → ℝ) → ℝ), IsCompact A → IsCompact Q → 0 ≤ K → Continuous h₁ → Continuous h₂ → (∀ t, 0 ≤ h₁ t) → (∀ t, 0 ≤ h₂ t) → (∀ t ∈ A, f t ∈ Q ∧ h₁ t ≤ h₂ (f t)) → (∀ t ∈ A, ∀ t' ∈ A, ‖t - t'‖ ≤ K * ‖f t - f t'‖) → ∫ t in A, h₁ t ≤ K ^ N * ∫ t in Q, h₂ t := by
  first | exact @GlobalTheory.setIntegral_le_of_expanding | exact GlobalTheory.setIntegral_le_of_expanding | (intros; apply GlobalTheory.setIntegral_le_of_expanding <;> assumption)
