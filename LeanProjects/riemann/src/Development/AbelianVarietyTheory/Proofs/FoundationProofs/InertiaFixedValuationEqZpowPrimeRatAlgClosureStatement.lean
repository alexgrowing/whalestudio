import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsDirichletCharacterSmoothed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaFixed_valuation_eq_zpow_prime_ratAlgClosure : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) → ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  first | exact @GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | exact GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed | (intros; apply GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed <;> assumption)
