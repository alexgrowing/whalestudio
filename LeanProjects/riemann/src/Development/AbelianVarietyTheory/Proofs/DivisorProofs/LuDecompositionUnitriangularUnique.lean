import Mathlib
open Matrix

namespace GlobalTheory

theorem lu_diag_mul_upper {R : Type} [CommRing R] {m : ℕ} (M N : Matrix (Fin m) (Fin m) R)
    (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) (i : Fin m) :
    (M * N) i i = M i i * N i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hM i k h, zero_mul]
    · rw [hN k i h, mul_zero]
  · simp

theorem lu_unique : ∀ (R : Type) [CommRing R] (m : ℕ) (A₁ A₂ N₁ U N₀ : Matrix (Fin m) (Fin m) R),
    (∀ i j, i < j → A₁ i j = 0) → (∀ i j, i < j → A₂ i j = 0) → (∀ i j, j < i → N₁ i j = 0) →
    (∀ i, N₁ i i = 1) → (∀ i j, j < i → U i j = 0) → (∀ i, U i i = 1) →
    (∀ i j, j < i → N₀ i j = 0) → (∀ i, N₀ i i = 1) → A₁ * A₂ * N₁ = U * N₀ → N₁ = U * N₀ := by
  intro R _ m A₁ A₂ N₁ U N₀ h1 h2 hN1 hN1d hU hUd hN0 hN0d h
  have hA : ∀ i j, i < j → (A₁ * A₂) i j = 0 := by
    intro i j hij
    rw [mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    rcases lt_or_ge i k with hk | hk
    · rw [h1 i k hk, zero_mul]
    · rw [h2 k j (lt_of_le_of_lt hk hij), mul_zero]
  have hbt : N₁.BlockTriangular id := fun i j hij => hN1 i j hij
  have hdet : N₁.det = 1 := by
    rw [det_of_upperTriangular hbt]; simp [hN1d]
  letI : Invertible N₁ := invertibleOfIsUnitDet N₁ (by rw [hdet]; exact isUnit_one)
  have hinv : N₁⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular hbt
  have hinv' : ∀ i j, j < i → N₁⁻¹ i j = 0 := fun i j hij => hinv hij
  have hinvd : ∀ i, N₁⁻¹ i i = 1 := by
    intro i
    have := congrFun (congrFun (mul_inv_of_invertible N₁) i) i
    rw [lu_diag_mul_upper N₁ N₁⁻¹ hN1 hinv' i, hN1d, one_mul] at this
    simpa using this
  have hV : ∀ i j, j < i → (U * N₀) i j = 0 := by
    have : (U * N₀).BlockTriangular id :=
      BlockTriangular.mul (fun i j hij => hU i j hij) (fun i j hij => hN0 i j hij)
    exact fun i j hij => this hij
  have hVd : ∀ i, (U * N₀) i i = 1 := by
    intro i; rw [lu_diag_mul_upper U N₀ hU hN0 i, hUd, hN0d, one_mul]
  have hAeq : A₁ * A₂ = U * N₀ * N₁⁻¹ := by
    rw [← h, mul_inv_cancel_right_of_invertible]
  have hA1 : A₁ * A₂ = 1 := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [hA i j hij, one_apply_ne (ne_of_lt hij)]
    · subst hij
      rw [hAeq, lu_diag_mul_upper _ _ hV hinv' i, hVd, hinvd, one_mul, one_apply_eq]
    · rw [hAeq, one_apply_ne (ne_of_gt hij)]
      have : (U * N₀ * N₁⁻¹).BlockTriangular id :=
        BlockTriangular.mul (fun a b hab => hV a b hab) hinv
      exact this hij
  rw [hA1, one_mul] at h
  exact h

end GlobalTheory
