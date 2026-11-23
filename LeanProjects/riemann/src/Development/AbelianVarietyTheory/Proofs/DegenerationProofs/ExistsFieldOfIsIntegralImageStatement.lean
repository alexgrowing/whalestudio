import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfIsIntegralImage
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_of_isIntegral_image' : ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  first | exact @GlobalTheory.exists_field_of_isIntegral_image | exact GlobalTheory.exists_field_of_isIntegral_image | (intros; apply GlobalTheory.exists_field_of_isIntegral_image <;> assumption)
