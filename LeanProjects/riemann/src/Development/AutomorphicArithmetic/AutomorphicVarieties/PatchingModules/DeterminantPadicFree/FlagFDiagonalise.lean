import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem flagF_diag_mul {F : Type} [Field F] {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (show id k < id i from h), zero_mul]
    · rw [hB (show id i < id k from h), mul_zero]
  · simp

private theorem flagF_tri {F H : Type} [Field F] {n : ℕ} (T : H → Matrix (Fin n) (Fin n) F)
    (E : Matrix (Fin n) (Fin n) F) (hT : ∀ s, (T s).BlockTriangular id)
    (hsep : ∀ i j, i ≠ j → ∃ s, T s i i ≠ T s j j) (hc : ∀ s, T s * E = E * T s) :
    E.BlockTriangular id := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, j < i → n + (j : ℕ) ≤ i + m → E i j = 0 := by
    intro m
    induction m with
    | zero => intro i j _ h; have := i.2; omega
    | succ m ih =>
      intro i j hji h
      obtain ⟨s, hs⟩ := hsep i j hji.ne'
      have h1 : (T s * E) i j = T s i i * E i j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with h' | h'
          · rw [hT s (show id k < id i from h'), zero_mul]
          · rw [ih k j (hji.trans h') (by rw [Fin.lt_def] at h'; omega), mul_zero]
        · simp
      have h2 : (E * T s) i j = E i j * T s j j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with h' | h'
          · rw [ih i k (h'.trans hji) (by rw [Fin.lt_def] at h'; omega), zero_mul]
          · rw [hT s (show id j < id k from h'), mul_zero]
        · simp
      rw [hc, h2, mul_comm] at h1
      by_contra h0
      exact hs (mul_right_cancel₀ h0 h1).symm
  intro i j hji
  exact key n i j hji (by have : (j : ℕ) < i := hji; omega)

private theorem flagF_diagonalise {F : Type} [Field F] {n : ℕ} (E : Matrix (Fin n) (Fin n) F)
    (hE : E.BlockTriangular id) (hEE : E * E = E) :
    ∃ U : Matrix (Fin n) (Fin n) F, U.BlockTriangular id ∧ (∀ i, U i i = 1) ∧
      E * U = U * diagonal (fun i => E i i) := by
  have hd : ∀ i, E i i * E i i = E i i := fun i => by rw [← flagF_diag_mul hE hE, hEE]
  have hDD : diagonal (fun i => E i i) * diagonal (fun i => E i i) = diagonal (fun i => E i i) := by
    rw [diagonal_mul_diagonal]; simp only [hd]
  have hD : (diagonal (fun i => E i i)).BlockTriangular id := blockTriangular_diagonal _
  have h1 : (1 : Matrix (Fin n) (Fin n) F).BlockTriangular id := blockTriangular_one
  refine ⟨E * diagonal (fun i => E i i) + (1 - E) * (1 - diagonal (fun i => E i i)),
    (hE.mul hD).add ((h1.sub hE).mul (h1.sub hD)), fun i => ?_, ?_⟩
  · rw [Matrix.add_apply, flagF_diag_mul hE hD, flagF_diag_mul (h1.sub hE) (h1.sub hD)]
    simp only [Matrix.sub_apply, diagonal_apply_eq, one_apply_eq]
    linear_combination 2 * hd i
  · generalize diagonal (fun i => E i i) = D at hDD
    have a1 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hEE, sub_self]
    have a2 : (1 - D) * D = 0 := by rw [sub_mul, one_mul, hDD, sub_self]
    rw [mul_add, add_mul, ← mul_assoc, ← mul_assoc, hEE, a1, zero_mul, mul_assoc, mul_assoc, hDD, a2,
      mul_zero]

theorem UpperTheory.V.Pa.Det.flagF :
    ∀ {F H : Type} [Field F] [Infinite F] [Group H] {n a : ℕ} (r : H →* GL (Fin n) F) (ψ : Fin n → H →* Fˣ), (∀ g, mat r g ∈ Ev F F n a) → Function.Injective ψ → HasFlag r ψ → ∃ (w : GL (Fin n) F) (ty : Fin n → Bool), (∀ i j : Fin n, decide ((i : ℕ) < a) ≠ ty j → w i j = 0) ∧ ∀ g, (∀ i j, j < i → (w⁻¹ * r g * w : GL (Fin n) F) i j = 0) ∧ ∀ i, (w⁻¹ * r g * w : GL (Fin n) F) i i = (ψ i g : F) := by
  intro F H _ _ _ n a r ψ hev hinj ⟨g, hg⟩
  classical
  set e : Matrix (Fin n) (Fin n) F := diagonal fun i => if (i : ℕ) < a then 1 else 0 with he
  have hee : e * e = e := by
    rw [he, diagonal_mul_diagonal]; congr 1; ext i; split_ifs <;> simp
  have hce : ∀ s, (r s : Matrix (Fin n) (Fin n) F) * e = e * r s := by
    intro s
    ext i j
    rw [he, mul_diagonal, diagonal_mul]
    have h : ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (r s : Matrix (Fin n) (Fin n) F) i j = 0 :=
      fun h => (Submodule.mem_bot F).1 ((hev s i j).2 h)
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at h ⊢ <;> simp [h]
  set E : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) * e * (g⁻¹ : GL (Fin n) F) with hE
  have hEE : E * E = E := by
    simp only [hE, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc e, hee]
  have hT : ∀ s, ((g * r s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id :=
    fun s i j h => (hg s).1 i j h
  have hEt : E.BlockTriangular id := by
    refine flagF_tri (fun s => ((g * r s * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) E hT ?_ ?_
    · intro i j hij
      by_contra hcon
      push Not at hcon
      refine hij (hinj (MonoidHom.ext fun s => Units.ext ?_))
      rw [← (hg s).2 i, ← (hg s).2 j]
      exact hcon s
    · intro s
      simp only [hE, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc (r s : Matrix (Fin n) (Fin n) F), hce, mul_assoc]
  obtain ⟨U, hU, hU1, hEU⟩ := flagF_diagonalise E hEt hEE
  have hdet : U.det ≠ 0 := by rw [det_of_upperTriangular hU]; simp [hU1]
  obtain ⟨u, rfl⟩ : ∃ u : GL (Fin n) F, (u : Matrix (Fin n) (Fin n) F) = U :=
    ⟨GeneralLinearGroup.mkOfDetNeZero U hdet, rfl⟩
  have hUi : ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
    letI := u.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hU
  refine ⟨g⁻¹ * u, fun j => decide (E j j = 1), fun i j hij => ?_, fun s => ?_⟩
  · have h : e * ((g⁻¹ * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        ((g⁻¹ * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * diagonal (fun i => E i i) := by
      rw [Units.val_mul, mul_assoc, ← hEU]
      simp only [hE, mul_assoc, Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h i) j
    rw [he, mul_diagonal, diagonal_mul, mul_comm] at h2
    by_contra h0
    have h3 := mul_left_cancel₀ h0 h2
    apply hij
    by_cases hi : (i : ℕ) < a
    · simp [hi] at h3 ⊢; exact h3.symm
    · simp [hi] at h3 ⊢; simp [← h3]
  · have e1 : (g⁻¹ * u)⁻¹ * r s * (g⁻¹ * u) = u⁻¹ * ((g * r s * g⁻¹) * u) := by group
    have t1 : ((u⁻¹ * ((g * r s * g⁻¹) * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
      rw [Units.val_mul, Units.val_mul]
      exact hUi.mul ((hT s).mul hU)
    rw [e1]
    refine ⟨fun i j h => t1 h, fun i => ?_⟩
    have h1 := flagF_diag_mul hU t1 i
    rw [← Units.val_mul, mul_inv_cancel_left, Units.val_mul, flagF_diag_mul (hT s) hU, hU1, mul_one,
      one_mul] at h1
    rw [← (hg s).2 i]
    exact h1.symm
