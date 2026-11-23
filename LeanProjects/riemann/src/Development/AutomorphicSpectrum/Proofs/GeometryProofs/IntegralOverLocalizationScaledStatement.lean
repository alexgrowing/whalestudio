import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_over_localization_scaled : ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K), (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) → ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | exact GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | (intros; apply GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral <;> assumption)
