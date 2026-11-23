import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryMulVecEqOfFormEq
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_mulVec_eq_of_form_eq' : ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E, star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 → ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  first | exact @GlobalTheory.exists_unitary_mulVec_eq_of_form_eq | exact GlobalTheory.exists_unitary_mulVec_eq_of_form_eq | (intros; apply GlobalTheory.exists_unitary_mulVec_eq_of_form_eq <;> assumption)
