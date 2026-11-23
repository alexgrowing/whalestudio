import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficients
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoIOfEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertiaFixed_near_almostFixed_coefficients : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  first | exact @GlobalTheory.PerFix.exists_fixed_near | exact GlobalTheory.PerFix.exists_fixed_near | (intros; apply GlobalTheory.PerFix.exists_fixed_near <;> assumption)
