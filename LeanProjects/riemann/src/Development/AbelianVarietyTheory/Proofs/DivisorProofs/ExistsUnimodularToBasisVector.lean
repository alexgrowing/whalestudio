import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open GlobalTheory.TriFrame

namespace GlobalTheory

theorem column_unit_entry_to_first_basis_vector :
    ∀ {R : Type} [CommRing R] {r : ℕ} (a : Fin (r+1) → R) (l0 : Fin (r+1)), IsUnit (a l0) →
      ∃ Q : GL (Fin (r+1)) R, (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).mulVec a
        = (Pi.single 0 1 : Fin (r+1) → R) := by
  intro R _ r a l0 ha
  classical
  set σ : Equiv.Perm (Fin (r+1)) := Equiv.swap 0 l0 with hσ
  set b : Fin (r+1) → R := a ∘ σ with hb
  set E : Matrix (Fin (r+1)) (Fin (r+1)) R :=
    Matrix.of fun l j => if j = 0 then b l else if l = j then 1 else 0 with hEdef
  have hlow : E.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hj : j ≠ 0 := by
      rintro rfl
      exact absurd hij' (Fin.not_lt_zero i)
    have hne : i ≠ j := ne_of_lt hij'
    simp [hEdef, hj, hne]
  have hE : E.det = b 0 := by
    rw [Matrix.det_of_lowerTriangular E hlow, Fin.prod_univ_succ]
    have : ∀ i : Fin r, E i.succ i.succ = 1 := by
      intro i
      simp [hEdef, Fin.succ_ne_zero]
    simp [this, hEdef]
  set B : Matrix (Fin (r+1)) (Fin (r+1)) R := E.submatrix σ id with hBdef
  have hBdet : IsUnit B.det := by
    rw [hBdef, Matrix.det_permute, hE]
    have h0 : b 0 = a l0 := by simp [hb, hσ]
    rw [h0]
    refine IsUnit.mul ?_ ha
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hBcol : B.mulVec (Pi.single 0 1) = a := by
    funext i
    simp [hBdef, hEdef, Matrix.mulVec, dotProduct, Pi.single_apply, hb, hσ]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hBdet
  refine ⟨u⁻¹, ?_⟩
  rw [← hBcol, Matrix.mulVec_mulVec, ← hu]
  have : ((u⁻¹ : GL (Fin (r+1)) R) : Matrix (Fin (r+1)) (Fin (r+1)) R) * (u : Matrix _ _ R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this, Matrix.one_mulVec]

end GlobalTheory
