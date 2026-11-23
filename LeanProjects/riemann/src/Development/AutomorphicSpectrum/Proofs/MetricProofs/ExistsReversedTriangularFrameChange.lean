import Mathlib

open Matrix

namespace GlobalTheory.CompanionTheory.AdaptedFrame

variable {Φ : Type} [Field Φ] {r : ℕ}

def revMatrix (Φ : Type) [Field Φ] (r : ℕ) : Matrix (Fin r) (Fin r) Φ :=
  Matrix.of fun a b => if a = Fin.rev b then 1 else 0

theorem mul_revMatrix_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (A * revMatrix Φ r) a b = A a (Fin.rev b) := by
  simp [Matrix.mul_apply, revMatrix]

theorem revMatrix_mul_apply (A : Matrix (Fin r) (Fin r) Φ) (a b : Fin r) :
    (revMatrix Φ r * A) a b = A (Fin.rev a) b := by
  have : ∀ x : Fin r, (a = Fin.rev x) ↔ (x = Fin.rev a) := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, revMatrix, this]

theorem revMatrix_mul_self : revMatrix Φ r * revMatrix Φ r = 1 := by
  ext a b
  rw [mul_revMatrix_apply]
  simp [revMatrix, Matrix.one_apply, Fin.rev_rev]

theorem revMatrix_transpose : (revMatrix Φ r)ᵀ = revMatrix Φ r := by
  ext a b
  simp only [revMatrix, Matrix.transpose_apply, Matrix.of_apply]
  have : (b = Fin.rev a) ↔ (a = Fin.rev b) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

theorem inv_diag (U : Matrix (Fin r) (Fin r) Φ) (hU : U.BlockTriangular id)
    (hd : ∀ l, U l l ≠ 0) (l : Fin r) : U⁻¹ l l = (U l l)⁻¹ := by
  have hdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have h1 : (U * U⁻¹) l l = 1 := by
    rw [Matrix.mul_nonsing_inv U hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single l] at h1
  · exact eq_inv_of_mul_eq_one_right h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hU (show id k < id l from h)]; simp
    · rw [hinv (show id l < id k from h)]; simp
  · simp

theorem reversed_dual_frame :
    ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (r : ℕ) (u T U Rm Rm' : Matrix (Fin r) (Fin r) Φ),
      IsUnit u.det → IsUnit T.det → U.BlockTriangular id → (∀ l, U l l ≠ 0) →
      (∀ a b, Rm a b ∈ R) → (∀ a b, Rm' a b ∈ R) → Rm * Rm' = 1 →
      (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) * U = Tᵀ⁻¹ * Rm →
      ∃ U₂ R₂ R₂' : Matrix (Fin r) (Fin r) Φ, U₂.BlockTriangular id ∧
        (∀ l, U₂ l l = (U l.rev l.rev)⁻¹) ∧ (∀ a b, R₂ a b ∈ R) ∧ (∀ a b, R₂' a b ∈ R) ∧
        R₂ * R₂' = 1 ∧ u * U₂ = T * R₂ := by
  intro Φ _ R r u T U Rm Rm' hu hT hU hd hRm hRm' hmul h
  have hUdet : IsUnit U.det := by
    rw [Matrix.det_of_upperTriangular hU]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hd i)
  have hUinv : U⁻¹.BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  have hutdet : IsUnit (uᵀ).det := by rwa [Matrix.det_transpose]
  have hTtdet : IsUnit (Tᵀ).det := by rwa [Matrix.det_transpose]
  have hUtdet : IsUnit (Uᵀ).det := by rwa [Matrix.det_transpose]
  set P := revMatrix Φ r with hP
  have hPP : P * P = 1 := revMatrix_mul_self
  have hPt : Pᵀ = P := revMatrix_transpose
  have hrev : (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) = uᵀ⁻¹ * P := by
    ext a b
    rw [mul_revMatrix_apply]; rfl
  rw [hrev] at h

  have e1 : Tᵀ * (uᵀ⁻¹ * P * U * Rm') = 1 := by
    rw [h, Matrix.mul_assoc (Tᵀ⁻¹), hmul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hTtdet]
  have e2 : Rm'ᵀ * Uᵀ * P * u⁻¹ * T = 1 := by
    have := congrArg Matrix.transpose e1
    simp only [Matrix.transpose_mul, Matrix.transpose_one, hPt, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv] at this
    simpa [Matrix.mul_assoc] using this
  have e3 : T * (Rm'ᵀ * Uᵀ * P * u⁻¹) = 1 := mul_eq_one_comm.1 e2
  have e4 : T * Rm'ᵀ = u * P * Uᵀ⁻¹ := by
    have hk : (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹) = 1 := by
      calc (Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)
          = Uᵀ * P * (u⁻¹ * u) * P * Uᵀ⁻¹ := by simp only [Matrix.mul_assoc]
        _ = Uᵀ * (P * P) * Uᵀ⁻¹ := by
            rw [Matrix.nonsing_inv_mul _ hu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = 1 := by rw [hPP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hUtdet]
    calc T * Rm'ᵀ = T * Rm'ᵀ * ((Uᵀ * P * u⁻¹) * (u * P * Uᵀ⁻¹)) := by rw [hk, Matrix.mul_one]
      _ = (T * (Rm'ᵀ * Uᵀ * P * u⁻¹)) * (u * P * Uᵀ⁻¹) := by simp only [Matrix.mul_assoc]
      _ = u * P * Uᵀ⁻¹ := by rw [e3, Matrix.one_mul]
  have hent : ∀ a b, (P * Uᵀ⁻¹ * P) a b = U⁻¹ (Fin.rev b) (Fin.rev a) := by
    intro a b
    rw [hP, mul_revMatrix_apply, revMatrix_mul_apply, ← Matrix.transpose_nonsing_inv,
      Matrix.transpose_apply]
  refine ⟨P * Uᵀ⁻¹ * P, Rm'ᵀ * P, P * Rmᵀ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    rw [hent]
    exact hUinv (show id (Fin.rev a) < id (Fin.rev b) from Fin.rev_lt_rev.2 hab')
  · intro l
    rw [hent]
    exact inv_diag U hU hd _
  · intro a b
    rw [mul_revMatrix_apply]; exact hRm' _ _
  · intro a b
    rw [revMatrix_mul_apply]; exact hRm _ _
  · calc Rm'ᵀ * P * (P * Rmᵀ) = Rm'ᵀ * (P * P) * Rmᵀ := by simp only [Matrix.mul_assoc]
      _ = (Rm * Rm')ᵀ := by rw [hPP, Matrix.mul_one, Matrix.transpose_mul]
      _ = 1 := by rw [hmul, Matrix.transpose_one]
  · calc u * (P * Uᵀ⁻¹ * P) = (u * P * Uᵀ⁻¹) * P := by simp only [Matrix.mul_assoc]
      _ = T * (Rm'ᵀ * P) := by rw [← e4, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.AdaptedFrame
