import Mathlib

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fromRows_mul_fromCols_split {R : Type} [CommRing R] {p q : ℕ}
    (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R)
    (J' : Matrix (Fin p) (Fin p ⊕ Fin q) R) (S' : Matrix (Fin p ⊕ Fin q) (Fin q) R)
    (h0 : S * J = 0) (hJ : J' * J = 1) (hS : S * S' = 1) :
    Matrix.fromRows (J' * (1 - S' * S)) S * Matrix.fromCols J S' = 1 := by
  rw [Matrix.fromRows_mul_fromCols]
  have e1 : J' * (1 - S' * S) * J = 1 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      h0, Matrix.mul_zero, sub_zero, hJ]
  have e2 : J' * (1 - S' * S) * S' = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      hS, Matrix.mul_zero, sub_self]
  rw [e1, e2, h0, hS, Matrix.fromBlocks_one]

theorem splitExact_of_rank : ∀ (R : Type) [CommRing R] (p q : ℕ) (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R), S * J = 0 → (∃ J' : Matrix (Fin p) (Fin p ⊕ Fin q) R, J' * J = 1) → (∃ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1) → (∀ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1 → IsUnit (Matrix.fromCols J S').det) ∧ ∀ v, S.mulVec v = 0 ↔ ∃ w, J.mulVec w = v := by
  rintro R inst p q J S h0 ⟨J', hJ⟩ ⟨S₀, hS₀⟩
  refine ⟨fun S' hS => ?_, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact Matrix.isUnit_det_of_left_inverse (fromRows_mul_fromCols_split J S J' S' h0 hJ hS)
  · have hMN := fromRows_mul_fromCols_split J S J' S₀ h0 hJ hS₀
    have hNM : Matrix.fromCols J S₀ * Matrix.fromRows (J' * (1 - S₀ * S)) S = 1 := by
      first
      | exact mul_eq_one_comm.mp hMN
      | (rw [← Matrix.inv_eq_left_inv hMN]
         exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse hMN))
    rw [Matrix.fromCols_mul_fromRows] at hNM
    refine ⟨(J' * (1 - S₀ * S)).mulVec v, ?_⟩
    calc J.mulVec ((J' * (1 - S₀ * S)).mulVec v)
        = J.mulVec ((J' * (1 - S₀ * S)).mulVec v) + S₀.mulVec (S.mulVec v) := by
          rw [hv, Matrix.mulVec_zero, add_zero]
      _ = (J * (J' * (1 - S₀ * S)) + S₀ * S).mulVec v := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = v := by rw [hNM, Matrix.one_mulVec]
  · rintro ⟨w, rfl⟩
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]

end GlobalTheory.CompanionTheory.Ar.Flat
