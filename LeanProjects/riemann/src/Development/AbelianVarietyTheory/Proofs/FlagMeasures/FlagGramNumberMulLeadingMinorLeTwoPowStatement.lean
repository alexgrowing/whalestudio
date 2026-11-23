import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberMulLeadingMinorLeTwoPow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGramNumber_mul_leadingMinor_le_two_pow : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ x ∈ GG k r, Yj k r hj z z' γ x * Yj k r hj z' z γ⁻¹ (γ * x) * Dj k r hj z z' γ ≤ 2 ^ j := by
  first | exact @GlobalTheory.Amp.ExtPow.gram_mul_minor_le | exact GlobalTheory.Amp.ExtPow.gram_mul_minor_le | (intros; apply GlobalTheory.Amp.ExtPow.gram_mul_minor_le <;> assumption)
