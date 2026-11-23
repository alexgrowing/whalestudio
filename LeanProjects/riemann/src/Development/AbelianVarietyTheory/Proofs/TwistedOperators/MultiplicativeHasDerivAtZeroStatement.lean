import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicativeHasDerivAtZero

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add : ∀ (lam : ℝ → ℂ), lam 0 = 1 → (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  first | exact @GlobalTheory.multiplicative_hasDerivAt_zero | exact GlobalTheory.multiplicative_hasDerivAt_zero | (intros; apply GlobalTheory.multiplicative_hasDerivAt_zero <;> assumption)
