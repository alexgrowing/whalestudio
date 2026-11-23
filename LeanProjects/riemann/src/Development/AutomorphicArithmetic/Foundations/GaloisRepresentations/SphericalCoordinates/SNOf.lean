import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis

open scoped Matrix

namespace UpperTheory.Gal.W2

theorem sN_of : SN := by
  intro F K _ _ n τ ψ hψ
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp, fun M => Subsingleton.elim _ _⟩
  have i0 : Fin n := ⟨0, hn⟩
  haveI : Nonempty (Fin n) := ⟨i0⟩
  have hsc : ∀ {R : Type} [Field R] (i k : Fin n) (x : R),
      Matrix.single i k x = Matrix.scalar (Fin n) x * Matrix.single i k 1 := by
    intro R _ i k x
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hsum1 : ∀ {R : Type} [Field R], (∑ k : Fin n, Matrix.single k k (1 : R)) = 1 := by
    intro R _
    ext r s
    rw [Matrix.sum_apply, Finset.sum_eq_single r]
    · by_cases h : r = s
      · subst h
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, Matrix.one_apply, h]
    · intro k _ hk
      simp [Matrix.single_apply, hk]
    · simp
  have hEE : ∀ i j j' k, ψ (Matrix.single i j 1) * ψ (Matrix.single j' k 1) =
      if j = j' then ψ (Matrix.single i k 1) else 0 := by
    intro i j j' k
    rw [← map_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, map_zero]
  have hP : ψ (Matrix.single i0 i0 1) ≠ 0 := by
    intro h0
    have hk : ∀ k, ψ (Matrix.single k k 1) = 0 := by
      intro k
      have e1 : ψ (Matrix.single k k 1) = ψ (Matrix.single k i0 1) * ψ (Matrix.single i0 i0 1) *
          ψ (Matrix.single i0 k 1) := by
        rw [hEE k i0 i0 i0, if_pos rfl, hEE k i0 i0 k, if_pos rfl]
      rw [e1, h0, mul_zero, zero_mul]
    have h1 : ψ 1 = 0 := by
      rw [← hsum1 (R := F), map_sum]
      exact Finset.sum_eq_zero fun k _ => hk k
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨a, b, hab⟩ : ∃ a b, ψ (Matrix.single i0 i0 1) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (Matrix.ext h)
  have hL : ∀ i k, ψ (Matrix.single i k 1) * (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.mul_sum]
    have l1 : ∀ j, ψ (Matrix.single i k 1) * (ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
        if k = j then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [← mul_assoc, hEE]
      split_ifs with h
      · subst h
        rfl
      · rw [zero_mul]
    simp only [l1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hR : ∀ i k, (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) * Matrix.single i k 1 =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.sum_mul]
    have l2 : ∀ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1 * Matrix.single i k 1 =
        if j = i then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [mul_assoc]
      split_ifs with h
      · subst h
        rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, mul_zero]
    simp only [l2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1, ?_, ?_⟩
  · have hTS : (∑ k, Matrix.single k a (ψ (Matrix.single i0 i0 1) a b)⁻¹ * ψ (Matrix.single i0 k 1)) *
        (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) = 1 := by
      rw [Finset.sum_mul, ← hsum1 (R := K)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, hL, ← mul_assoc, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    have hd := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact right_ne_zero_of_mul_eq_one hd
  · intro M
    have hM : M = ∑ i, ∑ k, Matrix.scalar (Fin n) (M i k) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single M]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k (M i k)
    have hMt : M.map τ = ∑ i, ∑ k, Matrix.scalar (Fin n) (τ (M i k)) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single (M.map τ)]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k _
    rw [hMt]
    conv_lhs => rw [hM]
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hψ, mul_assoc, hL, ← hR, ← mul_assoc, ← mul_assoc,
      (Matrix.scalar_commute (τ (M i k)) (fun r' => Commute.all _ r') _).eq]

end UpperTheory.Gal.W2
