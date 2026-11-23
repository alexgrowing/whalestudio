import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlacesOfSamePrimeBelow
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_valuationSubring_of_same_below : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  first | exact @GlobalTheory.conj_places_of_same_prime_below | exact GlobalTheory.conj_places_of_same_prime_below | (intros; apply GlobalTheory.conj_places_of_same_prime_below <;> assumption)
