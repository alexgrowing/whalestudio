import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

namespace GlobalTheory.WholeFlag.Glue

theorem fullFrame_gram : ∀ {R : Type} [CommRing R] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) R) (J : Matrix (Fin (g + g)) (Fin (g + g)) R) (τ : Fin g → Fin (g + g)), IsUnit J.det → IsUnit (rowSel τ * U : Matrix (Fin g) (Fin g) R).det → ∀ (i k : Fin g), ((fullFrame U J (leftInv U τ)).transpose * J * fullFrame U J (leftInv U τ)) (Fin.castAdd g i) (Fin.castAdd g k) = (U.transpose * J * U) i k ∧ ((fullFrame U J (leftInv U τ)).transpose * J * fullFrame U J (leftInv U τ)) (Fin.castAdd g i) (Fin.natAdd g k) = antiDiag R g i k := by
  intro R _ g U J τ hJ hU i k
  have hL : leftInv U τ * U = 1 := by
    exact (Matrix.mul_assoc (rowSel τ * U : Matrix (Fin g) (Fin g) R)⁻¹ (rowSel τ) U).trans
      (Matrix.nonsing_inv_mul _ hU)
  have h2 : U.transpose * J * (J⁻¹ * (leftInv U τ).transpose * antiDiag R g) = antiDiag R g := by
    have : U.transpose * J * (J⁻¹ * (leftInv U τ).transpose * antiDiag R g)
        = U.transpose * (J * J⁻¹) * (leftInv U τ).transpose * antiDiag R g := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one, ← Matrix.transpose_mul, hL, Matrix.transpose_one,
      Matrix.one_mul]
  have h1 : ∀ r, ((fullFrame U J (leftInv U τ)).transpose * J) (Fin.castAdd g i) r = (U.transpose * J) i r := by
    intro r
    simp only [Matrix.mul_apply, Matrix.transpose_apply, fullFrame_left]
  constructor
  · rw [Matrix.mul_apply, Matrix.mul_apply (M := U.transpose * J)]
    exact Finset.sum_congr rfl fun r _ => by rw [h1, fullFrame_left]
  · conv_rhs => rw [← h2]
    rw [Matrix.mul_apply, Matrix.mul_apply (M := U.transpose * J)]
    exact Finset.sum_congr rfl fun r _ => by rw [h1, fullFrame_right]

end GlobalTheory.WholeFlag.Glue
