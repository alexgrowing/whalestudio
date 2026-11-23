import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPrimePowAutomorphismInertialAtPrime
import ReciprocityTheory.GaloisValuations.Global
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicPrimePow_automorphism_inertial_at_prime : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l k : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ k) → ∀ τ : (IntermediateField.adjoin ℚ {ζ}) ≃ₐ[ℚ] (IntermediateField.adjoin ℚ {ζ}), (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) ∧ (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation ((τ x : IntermediateField.adjoin ℚ {ζ}) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) := by
  first | exact @GlobalTheory.CycInertial.main | exact GlobalTheory.CycInertial.main | (intros; apply GlobalTheory.CycInertial.main <;> assumption)
