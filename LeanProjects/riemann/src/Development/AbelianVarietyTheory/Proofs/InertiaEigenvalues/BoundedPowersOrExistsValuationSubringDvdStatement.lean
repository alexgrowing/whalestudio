import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedPowersOrExistsValuationSubringDvd
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_dvd_bound_or_exists_valuationSubring_dvd : ∀ (R : Type) [CommRing R] (u x : R) (M : ℕ), u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) → (∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n) ∨ ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : R →+* ↥V), f u ≠ 0 ∧ ¬ IsUnit (f u) ∧ f x ∣ f u ^ M := by
  first | exact @GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd | exact GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd | (intros; apply GlobalTheory.bounded_powers_or_exists_valuationSubring_dvd <;> assumption)
