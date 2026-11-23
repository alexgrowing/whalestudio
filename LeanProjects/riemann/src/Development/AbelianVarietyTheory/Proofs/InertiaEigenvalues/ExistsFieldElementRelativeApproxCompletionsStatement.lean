import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementRelativeApproxCompletions
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_element_relative_approx_completions : ∀ (L : Type) [Field L] [NumberField L] (R : Finset (HeightOneSpectrum (𝓞 L))) (z : ∀ P : HeightOneSpectrum (𝓞 L), P.adicCompletion L), (∀ P ∈ R, z P ≠ 0) → ∃ k : Lˣ, ∀ P ∈ R, Valued.v (z P - algebraMap L (P.adicCompletion L) (k : L)) ≤ WithZero.exp (-1 : ℤ) * Valued.v (z P) := by
  first | exact @GlobalTheory.WeakApprox.exists_units_approx | exact GlobalTheory.WeakApprox.exists_units_approx | (intros; apply GlobalTheory.WeakApprox.exists_units_approx <;> assumption)
