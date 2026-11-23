import Mathlib

open Matrix

namespace PositivityTheory.KB.MomentRationality.Ht

section Lin

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem re_star_dot_self (u : n → ℂ) : (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem re_quad (A : Matrix n n ℂ) (v : n → ℂ) :
    (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re = ∑ i, ‖(A *ᵥ v) i‖ ^ 2 := by
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, re_star_dot_self]

theorem sum_norm_unitary {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) (u : n → ℂ) :
    ∑ i, ‖(U *ᵥ u) i‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  rw [← re_quad, ← re_star_dot_self]
  have h : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact (mem_unitaryGroup_iff').1 hU
  rw [h, one_mulVec]

theorem single_le_sum_sq (u : n → ℂ) (i : n) : ‖u i‖ ^ 2 ≤ ∑ j, ‖u j‖ ^ 2 :=
  Finset.single_le_sum (f := fun j => ‖u j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

end Lin

section Tri

variable {m : ℕ}

theorem mulVec_upper {Q : Matrix (Fin m) (Fin m) ℂ} (hQ : Q.BlockTriangular id) {z : Fin m → ℂ}
    {i : Fin m} (hz : ∀ j, i < j → z j = 0) : (Q *ᵥ z) i = Q i i * z i := by
  rw [mulVec, dotProduct, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hQ (show id j < id i from h), zero_mul]
    · rw [hz j h, mul_zero]
  · simp

theorem mulVec_lower {Q : Matrix (Fin m) (Fin m) ℂ} (hQ : ∀ a b : Fin m, a < b → Q a b = 0) {z : Fin m → ℂ}
    {i : Fin m} (hz : ∀ j, j < i → z j = 0) : (Q *ᵥ z) i = Q i i * z i := by
  rw [mulVec, dotProduct, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hz j h, mul_zero]
    · rw [hQ i j h, zero_mul]
  · simp

theorem mul_diag_upper {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (i : Fin m) : (A * B) i i = A i i * B i i := by
  rw [mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · simp

theorem inv_upper {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A.BlockTriangular id) (hBA : B * A = 1) :
    B.BlockTriangular id ∧ ∀ i, B i i * A i i = 1 := by
  have : Invertible A := invertibleOfLeftInverse A B hBA
  have hB : A⁻¹ = B := Matrix.inv_eq_left_inv hBA
  have ht : B.BlockTriangular id := hB ▸ blockTriangular_inv_of_blockTriangular hA
  refine ⟨ht, fun i => ?_⟩
  rw [← mul_diag_upper ht hA, hBA, one_apply_eq]

end Tri

section Tele

theorem sub_le_sum_abs_consecutive_diff {N : ℕ} (s : Fin N → ℝ) (i j : Fin N) :
    s i - s j ≤ ∑ a : Fin N, ∑ b : Fin N, if (b : ℕ) = a + 1 then |s a - s b| else 0 := by
  classical
  set f : ℕ → ℝ := fun k => if h : k < N then s ⟨k, h⟩ else 0 with hf
  have hfs : ∀ a : Fin N, f a = s a := fun a => by simp [hf, a.2]
  have hW : (∑ a : Fin N, ∑ b : Fin N, if (b : ℕ) = a + 1 then |s a - s b| else 0) =
      ∑ k ∈ Finset.range N, if k + 1 < N then |f k - f (k + 1)| else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => if k + 1 < N then |f k - f (k + 1)| else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : (a : ℕ) + 1 < N
    · rw [Finset.sum_eq_single ⟨(a : ℕ) + 1, ha⟩]
      · simp [ha, hf, a.2]
      · intro b _ hb
        rw [if_neg]
        intro e
        exact hb (Fin.ext e)
      · simp
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      intro e
      exact ha (e ▸ b.2)
  rw [hW, ← hfs i, ← hfs j]
  have key : ∀ a b : ℕ, a ≤ b → b < N → |f a - f b| ≤
      ∑ k ∈ Finset.range N, if k + 1 < N then |f k - f (k + 1)| else 0 := by
    intro a b hab hb
    have htel : f a - f b = ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have := Finset.sum_range_sub' (fun k => f (a + k)) (b - a)
      simp only [add_zero] at this
      rw [show a + (b - a) = b by omega] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => by rw [add_assoc]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsub : Finset.Ico a b ⊆ Finset.range N := by
      intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_range]
      omega
    refine (Finset.sum_le_sum fun k hk => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by split_ifs <;> simp)
    · simp only [Finset.mem_Ico] at hk
      rw [if_pos (by omega)]
  rcases le_total (i : ℕ) j with h | h
  · exact (le_abs_self _).trans (key i j h j.2)
  · refine le_trans ?_ (key j i h i.2)
    rw [abs_sub_comm]
    exact le_abs_self _

end Tele

end PositivityTheory.KB.MomentRationality.Ht
