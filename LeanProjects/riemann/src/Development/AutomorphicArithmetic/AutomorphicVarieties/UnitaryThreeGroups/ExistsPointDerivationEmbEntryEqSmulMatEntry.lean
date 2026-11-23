import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem theta_entry {R : Type} [CommRing R] (g : GL (Fin 3) R) (i j : Fin 3) :
    (theta g : Matrix (Fin 3) (Fin 3) R) i j = ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) j.rev i.rev := by
  rw [theta_val]
  simp [Matrix.mul_apply, Jmat]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    apply hk
    rw [h, Fin.rev_rev]
  · simp

private theorem der_inv {O R Q : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q]
    (x : R →ₐ[O] O) (D : R →ₗ[O] Q) (hD : D ∈ PtDer x Q) (t : Oˣ) (g : GL (Fin 3) R)
    (hg : GeneralLinearGroup.map (x : R →+* O) g = tor O t) (p q : Fin 3) :
    D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) =
      (-((((t ^ wt1 q)⁻¹ : Oˣ) : O) * (((t ^ wt1 p)⁻¹ : Oˣ) : O))) • D ((g : Matrix (Fin 3) (Fin 3) R) p q) := by
  have hDm : ∀ f h : R, D (f * h) = x f • D h + x h • D f := hD
  have hD1 : D 1 = 0 := by
    have h := hDm 1 1
    simp only [mul_one, map_one, one_smul] at h
    have h' : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hx : ∀ i j, x ((g : Matrix (Fin 3) (Fin 3) R) i j) =
      ((tor O t : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i j := by
    intro i j
    rw [← hg]
    rfl
  have hxi : ∀ i j, x (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) i j) =
      (((tor O t)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) i j := by
    intro i j
    rw [← hg, ← map_inv]
    rfl
  have htor : ((tor O t : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) =
      diagonal fun i => ((t ^ wt1 i : Oˣ) : O) := rfl
  have htori : (((tor O t)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) =
      diagonal fun i => (((t ^ wt1 i)⁻¹ : Oˣ) : O) := rfl
  have h1 : D ((1 : Matrix (Fin 3) (Fin 3) R) p q) = 0 := by
    rw [Matrix.one_apply]
    split_ifs
    · exact hD1
    · exact map_zero D
  have key := congrArg (fun M : Matrix (Fin 3) (Fin 3) R => D (M p q))
    (congrArg (fun h : GL (Fin 3) R => (h : Matrix (Fin 3) (Fin 3) R)) (mul_inv_cancel g))
  simp only [Units.val_mul, Units.val_one, h1, Matrix.mul_apply, map_sum, hDm, hx, hxi, htor, htori,
    Finset.sum_add_distrib, diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at key
  have e : ((t ^ wt1 p : Oˣ) : O) • D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) =
      -((((t ^ wt1 q)⁻¹ : Oˣ) : O) • D ((g : Matrix (Fin 3) (Fin 3) R) p q)) :=
    eq_neg_of_add_eq_zero_left key
  calc D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q)
      = (((t ^ wt1 p)⁻¹ : Oˣ) : O) • ((t ^ wt1 p : Oˣ) : O) •
          D (((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) p q) := by
        rw [smul_smul, Units.inv_mul, one_smul]
    _ = _ := by
        rw [e, smul_neg, smul_smul, neg_smul, mul_comm (((t ^ wt1 q)⁻¹ : Oˣ) : O)]

private theorem map_left_eq_tor_and_right_eq_of_map_eq {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (s : ℤˣ) (t : Oˣ) (x : R →ₐ[O] O) (y : GG 3 R) (hy : GG.map (x : R →+* O) y = ⟨tor O t, s⟩) :
    GeneralLinearGroup.map (x : R →+* O) y.left = tor O t ∧ y.right = s := by
  constructor
  · have h := congrArg SemidirectProduct.left hy
    simpa [GG.map] using h
  · have h := congrArg SemidirectProduct.right hy
    simpa [GG.map] using h

private theorem wt_rev_rev_eq_wt1_sub_wt1 (i j : Fin 3) : wt j.rev i.rev = wt1 i - wt1 j := by
  fin_cases i <;> fin_cases j <;> decide

theorem UpperTheory.exists_pointDerivation_emb_entry_eq_smul_mat_entry :
    ∀ {O : Type} [CommRing O] (s : ℤˣ) (t : Oˣ) (a b : Fin 3 ⊕ Fin 3), ∃ (u : O) (a' b' : Fin 3), wt a' b' = wt6 a - wt6 b ∧
          ∀ {R Q : Type} [CommRing R] [Algebra O R] [AddCommGroup Q] [Module O Q] (x : R →ₐ[O] O), ∀ D ∈ PtDer x Q, ∀ y : GG 3 R,
            GG.map (x : R →+* O) y = ⟨tor O t, s⟩ → D (emb y a b) = u • D (y.mat a' b') := by
  intro O _ s t a b
  by_cases hs : s = 1
  · rcases a with i | i <;> rcases b with j | j
    · refine ⟨1, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp [GG.mat]
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp
    · refine ⟨-((((t ^ wt1 i.rev)⁻¹ : Oˣ) : O) * (((t ^ wt1 j.rev)⁻¹ : Oˣ) : O)), j.rev, i.rev,
        by simp [wt6, wt_rev_rev_eq_wt1_sub_wt1], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨hl, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_pos (hr.trans hs)]
      simp only [fromBlocks_apply₂₂]
      rw [theta_entry]
      exact der_inv x D hD t y.left hl j.rev i.rev
  · rcases a with i | i <;> rcases b with j | j
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp
    · refine ⟨1, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp [GG.mat]
    · refine ⟨-((((t ^ wt1 i.rev)⁻¹ : Oˣ) : O) * (((t ^ wt1 j.rev)⁻¹ : Oˣ) : O)), j.rev, i.rev,
        by simp [wt6, wt_rev_rev_eq_wt1_sub_wt1], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨hl, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp only [fromBlocks_apply₂₁]
      rw [theta_entry]
      exact der_inv x D hD t y.left hl j.rev i.rev
    · refine ⟨0, i, j, by simp [wt6, wt], ?_⟩
      intro R Q _ _ _ _ x D hD y hy
      obtain ⟨_, hr⟩ := map_left_eq_tor_and_right_eq_of_map_eq s t x y hy
      rw [emb_apply, if_neg (by rw [hr]; exact hs)]
      simp
