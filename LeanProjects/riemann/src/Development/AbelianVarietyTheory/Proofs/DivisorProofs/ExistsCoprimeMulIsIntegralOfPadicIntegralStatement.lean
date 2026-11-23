import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegral
import Mathlib
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  first | (exact @GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (exact GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul) | (intros; apply GlobalTheory.IntegralDescent.exists_not_dvd_isIntegral_mul  <;> assumption)
