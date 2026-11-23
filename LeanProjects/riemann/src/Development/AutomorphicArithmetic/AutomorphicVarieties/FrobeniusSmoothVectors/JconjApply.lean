import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem jconj_apply {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Jmat R n * Mᵀ * Jmat R n) i j = M j.rev i.rev := by
  have h1 : ∀ k, (Jmat R n * Mᵀ) i k = M k i.rev := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
    · simp [Jmat]
    · intro b _ hb
      simp [Jmat, hb]
    · simp
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · rw [h1]
    simp [Jmat]
  · intro b _ hb
    have : j ≠ b.rev := by
      intro h
      apply hb
      rw [h, Fin.rev_rev]
    simp [Jmat, this]
  · simp

theorem UpperTheory.V.Fr.pr_norm2 :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] (p : C' →ₐ[O] C) (n : ℕ) (Z : Matrix (Fin n) (Fin n) C'), maximalIdeal C' * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal C' → thetaLie Z = Z → (∀ i j, i ≠ j → p (Z i j) = 0) → (∀ i j, i ≠ j → res O C' (Z i i) ≠ res O C' (Z j j)) → ∃ h : GL (Fin n) C', (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ theta h = h ∧ ∀ i j, i ≠ j → ((h : Matrix (Fin n) (Fin n) C') * Z * ((h⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C')) i j = 0 := by
  intro O _ _ C' _ _ _ C _ _ p n Z hmI hIm hZ hoff hdiag
  classical
  have hII : ∀ a b : C', a ∈ RingHom.ker p → b ∈ RingHom.ker p → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker p := Ideal.mul_mem_mul (hIm ha) hb
    rw [hmI] at hab
    simpa using hab
  have hZI : ∀ i j, i ≠ j → Z i j ∈ RingHom.ker p := by
    intro i j hij
    rw [RingHom.mem_ker]
    exact hoff i j hij
  have hunit : ∀ i j, i ≠ j → IsUnit (Z i i - Z j j) := by
    intro i j hij
    by_contra hu
    have hm : Z i i - Z j j ∈ maximalIdeal C' := (IsLocalRing.mem_maximalIdeal _).2 hu
    rw [← res_eq_zero_iff O C', map_sub, sub_eq_zero] at hm
    exact hdiag i j hij hm
  have hZr : ∀ i j, Z j.rev i.rev = -Z i j := by
    intro i j
    have hij := congrFun (congrFun hZ i) j
    simp only [thetaLie, Matrix.neg_apply, jconj_apply] at hij
    rw [← hij, neg_neg]
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) C', ∀ i j,
      A i j = if i = j then 0 else Z i j * Ring.inverse (Z i i - Z j j) :=
    ⟨Matrix.of fun i j => if i = j then 0 else Z i j * Ring.inverse (Z i i - Z j j), fun i j => rfl⟩
  have hAI : ∀ i j, A i j ∈ RingHom.ker p := by
    intro i j
    rw [hA]
    split_ifs with h
    · exact Ideal.zero_mem _
    · exact Ideal.mul_mem_right _ _ (hZI i j h)
  have hAA : A * A = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => hII _ _ (hAI i k) (hAI k j)
  have hAr : ∀ i j, A j.rev i.rev = -A i j := by
    intro i j
    rw [hA, hA]
    by_cases hij : i = j
    · subst hij
      simp
    · have hrev : j.rev ≠ i.rev := fun h => hij (Fin.rev_injective h).symm
      rw [if_neg hrev, if_neg hij, hZr i j, hZr j j, hZr i i]
      have hd : -Z j j - -Z i i = Z i i - Z j j := by ring
      rw [hd]
      ring
  have h1 : (1 + A) * (1 - A) = 1 := by
    rw [show (1 + A) * (1 - A) = 1 - A * A by noncomm_ring, hAA, sub_zero]
  have h2 : (1 - A) * (1 + A) = 1 := by
    rw [show (1 - A) * (1 + A) = 1 - A * A by noncomm_ring, hAA, sub_zero]
  refine ⟨⟨1 + A, 1 - A, h1, h2⟩, ?_, ?_, ?_⟩
  · ext i j
    have h0 : p (A i j) = 0 := by
      have := hAI i j
      rwa [RingHom.mem_ker] at this
    simp only [Units.val_mk, Matrix.map_apply, Matrix.add_apply, map_add, h0, add_zero,
      Matrix.one_apply]
    split_ifs <;> simp
  · apply Units.ext
    rw [theta_val]
    show Jmat C' n * (1 - A)ᵀ * Jmat C' n = 1 + A
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Jmat_mul_Jmat, sub_eq_add_neg]
    congr 1
    ext i j
    rw [Matrix.neg_apply, jconj_apply, hAr, neg_neg]
  · intro i j hij
    show ((1 + A) * Z * (1 - A)) i j = 0
    rw [show (1 + A) * Z * (1 - A) = Z + A * Z - Z * A - A * Z * A by noncomm_ring]
    have hAZ : (A * Z) i j = A i j * Z j j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single j]
      · intro k _ hk
        exact hII _ _ (hAI i k) (hZI k j hk)
      · simp
    have hZA : (Z * A) i j = Z i i * A i j := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · intro k _ hk
        exact hII _ _ (hZI i k (Ne.symm hk)) (hAI k j)
      · simp
    have hAZA : (A * Z * A) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => hII _ _ ?_ (hAI k j)
      rw [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hAI i l)
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.add_apply, hAZ, hZA, hAZA, hA, if_neg hij]
    have hu := Ring.inverse_mul_cancel _ (hunit i j hij)
    linear_combination (-(Z i j)) * hu
