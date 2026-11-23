import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousRealToComplexExponential
import Mathlib
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := by
  first | exact @GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | exact GlobalTheory.hasDerivAt_of_continuous_additive_to_mul | (intros; apply GlobalTheory.hasDerivAt_of_continuous_additive_to_mul <;> assumption)
