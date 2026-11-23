import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOfPartialDerivativeClosure
import Mathlib
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cont_diff_of_partial_derivative_closure : ∀ (k : ℕ) (S : Set ((Fin k → ℝ) → ℂ)), (∀ f ∈ S, Continuous f) →
    (∀ f ∈ S, ∀ j : Fin k, ∃ (ι : Type) (_ : Fintype ι) (c : ι → (Fin k → ℝ) → ℂ) (g : ι → (Fin k → ℝ) → ℂ),
      (∀ i, ContDiff ℝ ∞ (c i)) ∧ (∀ i, g i ∈ S) ∧
      ∀ t, HasDerivAt (fun s : ℝ => f (t + s • Pi.single j 1)) (∑ i, c i t * g i t) 0) →
    ∀ f ∈ S, ContDiff ℝ ∞ f := by
  first | exact @GlobalTheory.contDiff_of_partials_in_smooth_span | exact GlobalTheory.contDiff_of_partials_in_smooth_span | (intros; apply GlobalTheory.contDiff_of_partials_in_smooth_span <;> assumption)
