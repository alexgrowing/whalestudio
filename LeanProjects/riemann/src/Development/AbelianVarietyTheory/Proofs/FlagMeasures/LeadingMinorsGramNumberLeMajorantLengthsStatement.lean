import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsGramNumberLeMajorantLengths
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_minors_gram_number_le_majorant_lengths : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ l : Fin (r + 1), ‖Dmin k r z z' γ l.castSucc‖ ≤ (Sg k r z' x * Sg k r z (γ * x)) ^ r) ∧ 0 ≤ Yj k r hj z z' γ x ∧ Yj k r hj z z' γ x ≤ Sg k r z (γ * x) ^ r / Dj k r hj z z' γ ∧ ∀ H₁ : ℝ, 1 ≤ H₁ → sgV k r z z' γ H₁ ≤ max 1 ((Sg k r z' x * Sg k r z (γ * x)) ^ r / (2 * H₁) ^ (2 * r)) := by
  first | exact @GlobalTheory.Amp.MinorBound.minor_gram_bound | exact GlobalTheory.Amp.MinorBound.minor_gram_bound | (intros; apply GlobalTheory.Amp.MinorBound.minor_gram_bound <;> assumption)
