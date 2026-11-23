import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_units_finitely_many_norms : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  first | exact @GlobalTheory.units_fixed_eq_mul_mul_conj | exact GlobalTheory.units_fixed_eq_mul_mul_conj | (intros; apply GlobalTheory.units_fixed_eq_mul_mul_conj <;> assumption)
