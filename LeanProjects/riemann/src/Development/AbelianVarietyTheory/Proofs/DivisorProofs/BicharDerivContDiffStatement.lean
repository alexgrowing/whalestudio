import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiff
import Mathlib
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) → (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) → ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  first | exact @GlobalTheory.bichar_deriv_contDiff | exact GlobalTheory.bichar_deriv_contDiff | (intros; apply GlobalTheory.bichar_deriv_contDiff <;> assumption)
