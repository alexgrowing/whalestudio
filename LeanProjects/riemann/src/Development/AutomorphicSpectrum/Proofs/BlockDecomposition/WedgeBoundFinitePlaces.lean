import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge

variable {K ι ι' κ κ' : Type} [NormedField K]

theorem nF_nonneg' [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem minor_le_nF [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) (s : κ → ι) :
    ‖(A.submatrix s id).det‖ ≤ nF A :=
  le_ciSup (f := fun s : κ → ι => ‖(A.submatrix s id).det‖) (Set.finite_range _).bddAbove s

theorem nF_le_of_minors [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ s : κ → ι, ‖(A.submatrix s id).det‖ ≤ c) : nF A ≤ c :=
  Real.iSup_le h hc

theorem exists_minor_eq_nF [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K)
    (h : nF A ≠ 0) : ∃ s : κ → ι, ‖(A.submatrix s id).det‖ = nF A := by
  have : Nonempty (κ → ι) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h (Real.iSup_of_isEmpty _)
  exact exists_eq_ciSup_of_finite (f := fun s : κ → ι => ‖(A.submatrix s id).det‖)

theorem sz_nonneg' (g : Matrix ι κ K) : 0 ≤ sz g := Real.iSup_nonneg fun _ => norm_nonneg _

theorem sz_le_one {g : Matrix ι κ K} (h : ∀ i j, ‖g i j‖ ≤ 1) : sz g ≤ 1 :=
  Real.iSup_le (fun p => h p.1 p.2) zero_le_one

theorem int_mul [IsUltrametricDist K] [Fintype κ] {a : Matrix ι κ K} {b : Matrix κ ι' K}
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a * b) i j‖ ≤ 1 := by
  intro i j
  rw [mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (ha i k) (norm_nonneg _) (hb k j)

theorem int_add [IsUltrametricDist K] {a b : Matrix ι κ K}
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a + b) i j‖ ≤ 1 := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i j) (hb i j))

theorem int_sub [IsUltrametricDist K] {a b : Matrix ι κ K}
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a - b) i j‖ ≤ 1 := fun i j =>
  by
  have h : (a - b) i j = a i j + -b i j := by simp [sub_eq_add_neg]
  rw [h]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i j) (by simpa using hb i j))

theorem int_one [DecidableEq ι] : ∀ i j, ‖(1 : Matrix ι ι K) i j‖ ≤ 1 := by
  intro i j
  rw [one_apply]
  split_ifs <;> simp

theorem nF_mul_le (hM : MulF) [IsUltrametricDist K] [Fintype ι] [Fintype ι'] [Fintype κ]
    [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) (hg : ∀ i j, ‖g i j‖ ≤ 1) :
    nF (g * A) ≤ nF A := by
  refine ((hM K ι ι' κ A).1 g).trans ?_
  have h1 : sz g ^ Fintype.card κ ≤ 1 := pow_le_one₀ (sz_nonneg' g) (sz_le_one hg)
  simpa using mul_le_mul_of_nonneg_right h1 (nF_nonneg' A)

theorem sel_mul [DecidableEq ι] [Fintype ι] (s : κ → ι) (M : Matrix ι ι' K) :
    (1 : Matrix ι ι K).submatrix s id * M = M.submatrix s id := by
  ext a b
  simp [mul_apply, one_apply]

theorem norm_det_perm [Fintype κ] [DecidableEq κ] (M : Matrix κ κ K) (e : Equiv.Perm κ) :
    ‖(M.submatrix e id).det‖ = ‖M.det‖ := by
  rw [det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h <;> simp [h]

theorem nF_fromCols_sel_le [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (s : κ → ι) (C : Matrix ι κ' K)
    (hs : Function.Injective s) (hC : C.submatrix s id = 0) :
    nF (fromCols ((1 : Matrix ι ι K).submatrix s id)ᵀ C) ≤ nF C := by
  classical
  set E := (1 : Matrix ι ι K).submatrix s id with hE
  refine nF_le_of_minors _ (nF_nonneg' C) fun u => ?_
  by_cases hu : ∀ k, ∃ x, u x = s k
  swap
  · push_neg at hu
    obtain ⟨k, hk⟩ := hu
    have : ((fromCols Eᵀ C).submatrix u id).det = 0 := by
      refine det_eq_zero_of_column_eq_zero (Sum.inl k) fun x => ?_
      simpa [hE, one_apply] using hk x
    rw [this, norm_zero]
    exact nF_nonneg' C
  by_cases inj : Function.Injective u
  swap
  · rw [Function.Injective] at inj
    push_neg at inj
    obtain ⟨x, y, hxy, hne⟩ := inj
    have : ((fromCols Eᵀ C).submatrix u id).det = 0 :=
      det_zero_of_row_eq hne (by ext j; simp [hxy])
    rw [this, norm_zero]
    exact nF_nonneg' C
  choose σ hσ using hu
  have hσi : Function.Injective σ := fun a b h => hs (by rw [← hσ a, ← hσ b, h])
  let e0 : {x : κ ⊕ κ' // x ∈ Set.range (Sum.inl : κ → κ ⊕ κ')} ≃ {x // x ∈ Set.range σ} :=
    (Equiv.ofInjective _ Sum.inl_injective).symm.trans (Equiv.ofInjective σ hσi)
  let e : Equiv.Perm (κ ⊕ κ') := e0.extendSubtype
  have he : ∀ k, e (Sum.inl k) = σ k := by
    intro k
    have h := e0.extendSubtype_apply_of_mem (Sum.inl k) ⟨k, rfl⟩
    have h2 : (Equiv.ofInjective _ Sum.inl_injective).symm
        (⟨Sum.inl k, ⟨k, rfl⟩⟩ : {x : κ ⊕ κ' // x ∈ Set.range (Sum.inl : κ → κ ⊕ κ')}) = k :=
      Equiv.ofInjective_symm_apply Sum.inl_injective k
    simpa [e0, h2] using h
  have hb : ((fromCols Eᵀ C).submatrix u id).submatrix e id =
      fromBlocks 1 0 (Eᵀ.submatrix (u ∘ e ∘ Sum.inr) id) (C.submatrix (u ∘ e ∘ Sum.inr) id) := by
    ext (a | a) (b | b)
    · simp [he, hσ, hE, one_apply, hs.eq_iff, eq_comm]
    · simpa [he, hσ] using congrFun (congrFun hC a) b
    · simp
    · simp
  rw [← norm_det_perm _ e, hb, det_fromBlocks_zero₁₂, det_one, one_mul]
  exact minor_le_nF C _

theorem entry_eq_minor [Fintype κ] [DecidableEq κ] (D : Matrix ι κ K) (s : κ → ι)
    (hD : D.submatrix s id = 1) (i : ι) (k : κ) :
    D i k = (D.submatrix (Function.update s k i) id).det := by
  have h : D.submatrix (Function.update s k i) id = (1 : Matrix κ κ K).updateRow k (D i) := by
    ext a b
    by_cases hak : a = k
    · subst hak
      simp
    · have := congrFun (congrFun hD a) b
      simpa [Function.update_of_ne hak, updateRow_ne hak] using this
  rw [h, ← det_transpose, ← updateCol_transpose, transpose_one, ← cramer_apply, cramer_one]
  rfl

theorem nF_fromCols_of_id (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (D : Matrix ι κ K) (C : Matrix ι κ' K)
    (s : κ → ι) (hD : D.submatrix s id = 1) (hint : ∀ i j, ‖D i j‖ ≤ 1)
    (hC : C.submatrix s id = 0) : nF (fromCols D C) = nF C := by
  have hs : Function.Injective s := by
    intro a b hab
    by_contra hne
    have h1 := congrFun (congrFun hD a) a
    have h2 := congrFun (congrFun hD b) a
    simp only [submatrix_apply, id, hab, one_apply_eq] at h1
    rw [submatrix_apply, id, one_apply_ne (Ne.symm hne)] at h2
    exact one_ne_zero (h1.symm.trans h2)
  set E := (1 : Matrix ι ι K).submatrix s id with hE
  have hEE : E * Eᵀ = 1 := by
    rw [hE, sel_mul]
    ext a b
    simp [one_apply, hs.eq_iff, eq_comm]
  have hEC : E * C = 0 := by rw [hE, sel_mul, hC]
  have hEint : ∀ i j, ‖E i j‖ ≤ 1 := fun i j => int_one _ _
  have hEtint : ∀ i j, ‖Eᵀ i j‖ ≤ 1 := fun i j => int_one _ _
  apply le_antisymm
  · have hk : (1 + (D - Eᵀ) * E) * fromCols Eᵀ C = fromCols D C := by
      rw [mul_fromCols]
      congr 1
      · rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hEE, Matrix.mul_one]
        abel
      · rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hEC, Matrix.mul_zero, add_zero]
    rw [← hk]
    exact (nF_mul_le hM _ _ (int_add int_one (int_mul (int_sub hint hEtint) hEint))).trans
      (nF_fromCols_sel_le s C hs hC)
  · refine nF_le_of_minors _ (nF_nonneg' _) fun t => ?_
    have hb : (fromCols D C).submatrix (Sum.elim s t) id =
        fromBlocks 1 0 (D.submatrix t id) (C.submatrix t id) := by
      ext (a | a) (b | b)
      · simpa using congrFun (congrFun hD a) b
      · simpa using congrFun (congrFun hC a) b
      · simp
      · simp
    have := minor_le_nF (fromCols D C) (Sum.elim s t)
    rwa [hb, det_fromBlocks_zero₁₂, det_one, one_mul] at this

theorem nF_ne_zero_iff (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ K) : nF A ≠ 0 ↔ LinearIndependent K Aᵀ := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := exists_minor_eq_nF A h
    have hdet : ((A.submatrix s id)ᵀ).det ≠ 0 := by
      rw [det_transpose]
      intro h0
      rw [h0, norm_zero] at hs
      exact h hs.symm
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    refine LinearIndependent.of_comp (LinearMap.funLeft K K s) ?_
    exact hli
  · intro h h0
    have hinj : Function.Injective A.mulVecLin := by
      have := (Matrix.vecMul_injective_iff (M := Aᵀ)).2 h
      intro x y hxy
      apply this
      simpa [vecMul_transpose] using hxy
    obtain ⟨g, hg⟩ := A.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
    have hL : LinearMap.toMatrix' g * A = 1 := by
      have : LinearMap.toMatrix' (g ∘ₗ A.mulVecLin) = 1 := by
        rw [hg, LinearMap.toMatrix'_id]
      rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this
      exact this
    have h1 := (hM K ι κ κ A).1 (LinearMap.toMatrix' g)
    rw [hL, h0, mul_zero, (hM K κ κ κ 1).2.2 1, det_one, norm_one] at h1
    exact absurd h1 (by norm_num)

theorem nF_reindex [Fintype ι] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (e : κ' ≃ κ) (A : Matrix ι κ K) : nF (A.submatrix id e) = nF A := by
  unfold nF
  refine (Equiv.arrowCongr e (Equiv.refl ι)).iSup_congr fun s => ?_
  have : (A.submatrix (Equiv.arrowCongr e (Equiv.refl ι) s) id).submatrix e e =
      (A.submatrix id e).submatrix s id := by
    ext a b
    simp
  rw [← this, det_submatrix_equiv_self]

theorem nF_quot (hM : MulF) [IsUltrametricDist K] [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (B : Matrix ι κ K) (hB : LinearIndependent K Bᵀ) :
    ∃ Y : Matrix κ ι K, ∀ (κ' : Type) [Fintype κ'] [DecidableEq κ'] (C : Matrix ι κ' K),
      nF (fromCols B C) = nF B * nF ((1 - B * Y) * C) ∧ nF ((1 - B * Y) * C) ≤ nF C ∧
        (1 - B * Y) * B = 0 := by
  have hne := (nF_ne_zero_iff hM B).2 hB
  obtain ⟨s, hs⟩ := exists_minor_eq_nF B hne
  set Bs := B.submatrix s id with hBs
  have hdet : Bs.det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hs
    exact hne hs.symm
  have hu : IsUnit Bs.det := isUnit_iff_ne_zero.2 hdet
  set E := (1 : Matrix ι ι K).submatrix s id with hE
  have hEint : ∀ i j, ‖E i j‖ ≤ 1 := fun i j => int_one _ _
  have hEB : E * B = Bs := by rw [hE, sel_mul]
  set B0 := B * Bs⁻¹ with hB0
  have hB0s : B0.submatrix s id = 1 := by
    have : B0.submatrix s id = Bs * Bs⁻¹ := by
      rw [← sel_mul, hB0, ← Matrix.mul_assoc, ← hE, hEB]
    rw [this, mul_nonsing_inv _ hu]
  have hEB0 : E * B0 = 1 := by rw [hE, sel_mul, hB0s]
  have hnB0 : nF B0 = 1 := by
    have h1 : ‖Bs.det‖ * ‖(Bs⁻¹).det‖ = 1 := by
      rw [← norm_mul, ← det_mul, mul_nonsing_inv _ hu, det_one, norm_one]
    rw [hB0, (hM K ι ι κ B).2.1, ← hs, h1]
  have hB0int : ∀ i j, ‖B0 i j‖ ≤ 1 := by
    intro i k
    rw [entry_eq_minor B0 s hB0s i k, ← hnB0]
    exact minor_le_nF B0 _
  have hBs1 : B0 * Bs = B := by
    rw [hB0, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  refine ⟨Bs⁻¹ * E, fun κ' _ _ C => ?_⟩
  have hBY : B * (Bs⁻¹ * E) = B0 * E := by rw [hB0, Matrix.mul_assoc]
  rw [hBY]
  set P := 1 - B0 * E with hP
  have hPint : ∀ i j, ‖P i j‖ ≤ 1 := int_sub int_one (int_mul hB0int hEint)
  have hEP : E * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hEB0, Matrix.one_mul, sub_self]
  have hPC : (P * C).submatrix s id = 0 := by
    rw [← sel_mul, ← hE, ← Matrix.mul_assoc, hEP, Matrix.zero_mul]
  have hfact : fromCols B C = fromCols B0 (P * C) *
      (fromBlocks Bs (E * C) 0 1 : Matrix (κ ⊕ κ') (κ ⊕ κ') K) := by
    rw [fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, Matrix.mul_one, hBs1,
      ← Matrix.mul_assoc, hP, Matrix.sub_mul, Matrix.one_mul]
    simp
  refine ⟨?_, nF_mul_le hM _ _ hPint, ?_⟩
  · rw [hfact, (hM K ι ι (κ ⊕ κ') _).2.1, det_fromBlocks_zero₂₁, det_one, mul_one, hs,
      nF_fromCols_of_id hM B0 (P * C) s hB0s hB0int hPC, mul_comm]
  · rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hEB, hBs1, sub_self]

theorem wedgeF_of_mulF : MulF → WedgeF := by
  intro hM K ι _ _ _ _
  exact
    { nonneg := fun κ _ _ A => nF_nonneg' A
      ne_zero := fun κ _ _ A => nF_ne_zero_iff hM A
      reindex := fun κ κ' _ _ _ _ e A => nF_reindex e A
      quot := fun κ _ _ B hB => nF_quot hM B hB }

end GlobalTheory.CompanionTheory.Wedge

end
