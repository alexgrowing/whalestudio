import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RadicalEltMovingDualToMajorant
import Mathlib
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_fixing_mulVec_conj_eq_of_majorant : ∀ (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → θ * θ = 1 → (J * θ).PosDef →
    ∀ (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ), X₂.conjTranspose * J * X₂ = 0 → Y₂.conjTranspose * J * Y₂ = 0 →
      X₂.conjTranspose * J * Y₂ = 1 →
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 → ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  first | exact @GlobalTheory.radical_elt_moving_dual_to_majorant | exact GlobalTheory.radical_elt_moving_dual_to_majorant | (intros; apply GlobalTheory.radical_elt_moving_dual_to_majorant <;> assumption)
