import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq : ∀ (A₀ K₀ E : Type) [CommRing A₀] [IsDedekindDomain A₀] [Field K₀] [CharZero K₀] [Algebra A₀ K₀] [IsFractionRing A₀ K₀]
  [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E] [Algebra A₀ E] [IsScalarTower A₀ K₀ E] (N : ℕ), IsUnit (N : A₀) →
  ∀ s : Finset E, IntermediateField.adjoin K₀ (s : Set E) = ⊤ → (∀ x ∈ s, ∃ u : A₀ˣ, x ^ N = algebraMap A₀ E u) →
  ∀ P : Ideal (integralClosure A₀ E), P.IsPrime → P ≠ ⊥ →
    ¬ Ideal.map (algebraMap A₀ (integralClosure A₀ E)) (P.comap (algebraMap A₀ (integralClosure A₀ E))) ≤ P ^ 2 := by
  first | exact @GlobalTheory.kummer_not_map_comap_le_sq | exact GlobalTheory.kummer_not_map_comap_le_sq | (intros; apply GlobalTheory.kummer_not_map_comap_le_sq <;> assumption)
