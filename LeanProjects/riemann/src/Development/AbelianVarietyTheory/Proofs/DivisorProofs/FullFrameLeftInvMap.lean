import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

namespace GlobalTheory.WholeFlag.Glue.FrameMap

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

theorem map_inv {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n R) (hX : IsUnit X.det) :
    (X⁻¹).map f = (X.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul X hX, Matrix.map_one _ (map_zero f) (map_one f)]

theorem map_rowSel {g : ℕ} (τ : Fin g → Fin (g + g)) :
    (rowSel τ : Matrix (Fin g) (Fin (g + g)) R).map f = rowSel τ := by
  ext l r
  simp only [rowSel, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_antiDiag (g : ℕ) : (antiDiag R g).map f = antiDiag R' g := by
  ext l r
  simp only [antiDiag, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem leftInv_eq {S : Type} [CommRing S] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) S) (τ : Fin g → Fin (g + g)) :
    leftInv U τ = @HMul.hMul (Matrix (Fin g) (Fin g) S) (Matrix (Fin g) (Fin (g + g)) S) (Matrix (Fin g) (Fin (g + g)) S)
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (rowSel τ * U : Matrix (Fin g) (Fin g) S)⁻¹ (rowSel τ) := rfl

theorem map_leftInv {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) R) (τ : Fin g → Fin (g + g))
    (h : IsUnit (rowSel τ * U : Matrix (Fin g) (Fin g) R).det) :
    (leftInv U τ).map f = leftInv (U.map f) τ := by
  have e : (rowSel τ * U : Matrix (Fin g) (Fin g) R).map f
      = (rowSel τ * U.map f : Matrix (Fin g) (Fin g) R') := by
    rw [← map_rowSel f τ]
    exact Matrix.map_mul
  rw [leftInv_eq, leftInv_eq, Matrix.map_mul, map_inv f _ h, e, map_rowSel]

end GlobalTheory.WholeFlag.Glue.FrameMap

namespace GlobalTheory.WholeFlag.Glue

theorem fullFrame_leftInv_map : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {g : ℕ}
    (U : Matrix (Fin (g + g)) (Fin g) R) (J : Matrix (Fin (g + g)) (Fin (g + g)) R) (τ : Fin g → Fin (g + g)),
    IsUnit J.det → IsUnit (rowSel τ * U : Matrix (Fin g) (Fin g) R).det →
    (fullFrame U J (leftInv U τ)).map f = fullFrame (U.map f) (J.map f) (leftInv (U.map f) τ) := by
  intro R R' _ _ f g U J τ hJ hU
  ext r c
  refine Fin.addCases (fun k => ?_) (fun k => ?_) c
  · rw [Matrix.map_apply, fullFrame_left, fullFrame_left, Matrix.map_apply]
  · rw [Matrix.map_apply, fullFrame_right, fullFrame_right, ← FrameMap.map_inv f J hJ,
      ← FrameMap.map_leftInv f U τ hU, ← FrameMap.map_antiDiag f g, ← Matrix.transpose_map, ← Matrix.map_mul,
      ← Matrix.map_mul, Matrix.map_apply]

end GlobalTheory.WholeFlag.Glue
