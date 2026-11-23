import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegrallyClosedOfConductorNonZeroDivisorOfAss
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P)) → (∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) → IsIntegrallyClosed R := by
  first | exact @GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | exact GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes | (intros; apply GlobalTheory.isIntegrallyClosed_of_conductor_nonZeroDivisor_of_associatedPrimes <;> assumption)
