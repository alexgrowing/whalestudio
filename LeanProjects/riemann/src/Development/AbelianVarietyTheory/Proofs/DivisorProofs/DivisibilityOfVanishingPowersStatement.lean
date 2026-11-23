import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityOfVanishingPowers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibility_of_vanishing_powers : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R), ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) → ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r := by
  first | exact @GlobalTheory.DetInv.dvd_pow_of_local_dvd_pow | exact GlobalTheory.DetInv.dvd_pow_of_local_dvd_pow | (intros; apply GlobalTheory.DetInv.dvd_pow_of_local_dvd_pow <;> assumption)
