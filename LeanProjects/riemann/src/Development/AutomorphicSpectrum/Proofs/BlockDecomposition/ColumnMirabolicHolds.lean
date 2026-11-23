import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Iwasawa PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound

section Algebra

variable {F : Type} [Field F] {n : ℕ}

theorem cM_apply_pos (k : ℕ) (x : Fin (k + 1) → F) {i j : Fin n} (hj : (j : ℕ) = k + 1)
    (hi : (i : ℕ) < k + 1) : cM n k x i j = x ⟨i, hi⟩ := by
  simp only [cM, Matrix.of_apply]
  rw [dif_pos ⟨hj, hi⟩]

theorem cM_apply_neg (k : ℕ) (x : Fin (k + 1) → F) {i j : Fin n}
    (h : ¬((j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1)) : cM n k x i j = 0 := by
  simp only [cM, Matrix.of_apply]
  rw [dif_neg h]

theorem cM_add (k : ℕ) (x y : Fin (k + 1) → F) :
    cM n k (x + y) = cM n k x + cM n k y := by
  ext i j
  rw [Matrix.add_apply]
  by_cases h : (j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1
  · rw [cM_apply_pos k _ h.1 h.2, cM_apply_pos k _ h.1 h.2, cM_apply_pos k _ h.1 h.2, Pi.add_apply]
  · rw [cM_apply_neg k _ h, cM_apply_neg k _ h, cM_apply_neg k _ h, add_zero]

theorem cM_zero (k : ℕ) : cM n k (0 : Fin (k + 1) → F) = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  by_cases h : (j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1
  · rw [cM_apply_pos k _ h.1 h.2, Pi.zero_apply]
  · rw [cM_apply_neg k _ h]

theorem col_coe (k : ℕ) (x : Fin (k + 1) → F) :
    ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + cM n k x := rfl

private theorem cM_mul_cM_eq_zero (k : ℕ) (x y : Fin (k + 1) → F) :
    cM n k x * cM n k y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : (l : ℕ) = k + 1
  · rw [cM_apply_neg k y (fun h => absurd h.2 (by omega)), mul_zero]
  · rw [cM_apply_neg k x (fun h => hl h.1), zero_mul]

theorem col_add (k : ℕ) (x y : Fin (k + 1) → F) :
    col n k (x + y) = col n k x * col n k y := by
  apply Units.ext
  rw [Units.val_mul, col_coe, col_coe, col_coe, cM_add, add_mul, one_mul, mul_add, mul_one,
    cM_mul_cM_eq_zero, add_zero]
  abel

theorem col_zero (k : ℕ) : col n k (0 : Fin (k + 1) → F) = 1 := by
  apply Units.ext
  rw [col_coe, cM_zero, add_zero, Units.val_one]

theorem inP_col (k : ℕ) (x : Fin (k + 1) → F) : inP (k + 1) (col n k x) := by
  unfold inP
  rw [col_coe]
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [Matrix.add_apply, cM_apply_neg k x (fun h' => absurd h'.2 (by omega)), add_zero]
  · rw [Matrix.add_apply, cM_apply_neg k x (fun h' => absurd h'.1 (by omega)), add_zero]

theorem inP_succ {k : ℕ} {g : GL (Fin n) F} (h : inP k g) : inP (k + 1) g := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun i j hi => h1 i j (by omega), fun i j hj => h2 i j (by omega)⟩

theorem col_upper (k : ℕ) (x : Fin (k + 1) → F) {i j : Fin n} (hij : j < i) :
    (1 + cM n k x) i j = 0 := by
  have hij' : (j : ℕ) < i := hij
  rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega)),
    cM_apply_neg k x (fun h => by obtain ⟨h1, h2⟩ := h; omega), add_zero]

theorem col_diag (k : ℕ) (x : Fin (k + 1) → F) (i : Fin n) : (1 + cM n k x) i i = 1 := by
  rw [Matrix.add_apply, Matrix.one_apply_eq,
    cM_apply_neg k x (fun h => by obtain ⟨h1, h2⟩ := h; omega), add_zero]

theorem det_col (k : ℕ) (x : Fin (k + 1) → F) :
    ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  rw [col_coe]
  exact (Matrix.det_of_isUpperTriangular (fun i j hij => col_upper k x hij)).trans
    (Finset.prod_eq_one (fun i _ => col_diag k x i))

theorem superdiagSum_col {k : ℕ} (hk : k + 1 < n) (x : Fin (k + 1) → F) :
    Whittaker.superdiagSum (1 + cM n k x) = x (Fin.last k) := by
  unfold Whittaker.superdiagSum
  rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin n)]
  · rw [Finset.sum_eq_single (⟨k + 1, hk⟩ : Fin n)]
    · rw [if_pos rfl, Matrix.add_apply, Matrix.one_apply_ne (Fin.ne_of_val_ne (by simp)),
        cM_apply_pos k x rfl (by simp), zero_add]
      rfl
    · intro j _ hj
      split_ifs with h
      · exact absurd (Fin.ext (by simpa using h)) hj
      · rfl
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · rw [Matrix.add_apply, Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega)), zero_add]
      apply cM_apply_neg k x
      rintro ⟨h1, h2⟩
      apply hi
      exact Fin.ext (by simp; omega)
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem psiN_col {k : ℕ} (hk : k + 1 < n) (ψ : AddChar F ℂ) (x : Fin (k + 1) → F) :
    Whittaker.psiN ψ (col n k x) = ψ (x (Fin.last k)) := by
  unfold Whittaker.psiN
  rw [col_coe, superdiagSum_col hk x]

theorem one_castLE {k : ℕ} (hk : k + 1 ≤ n) (i j : Fin (k + 1)) :
    (1 : Matrix (Fin n) (Fin n) F) (Fin.castLE hk i) (Fin.castLE hk j) =
      (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun e => h (Fin.castLE_injective hk e))]

theorem det_eq_submatrix {k : ℕ} (hk : k + 1 ≤ n) (M : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j : Fin n, k + 1 ≤ (i : ℕ) → M i j = (1 : Matrix (Fin n) (Fin n) F) i j) :
    M.det = (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  have hblk : ∀ i, ¬((i : Fin n) : ℕ) < k + 1 → ∀ j, ((j : Fin n) : ℕ) < k + 1 → M i j = 0 := by
    intro i hi j hj
    rw [hM i j (by omega), Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))]
  rw [Matrix.twoBlockTriangular_det M (fun i => (i : ℕ) < k + 1) hblk]
  have hone : Matrix.toSquareBlockProp M (fun i => ¬((i : Fin n) : ℕ) < k + 1) = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    rw [Matrix.toSquareBlockProp, Matrix.toBlock_apply, hM i j (by omega)]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun e => h (congrArg Subtype.val e))]
  rw [hone, Matrix.det_one, mul_one]
  let e : Fin (k + 1) ≃ {i : Fin n // (i : ℕ) < k + 1} :=
    { toFun := fun i => ⟨Fin.castLE hk i, i.2⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun i => rfl
      right_inv := fun i => rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem sum_castLE {k : ℕ} (hk : k + 1 ≤ n) (f : Fin n → F)
    (hf : ∀ l : Fin n, ¬(l : ℕ) < k + 1 → f l = 0) :
    ∑ l, f l = ∑ l : Fin (k + 1), f (Fin.castLE hk l) := by
  have hmap : ∑ l ∈ Finset.univ.map (⟨Fin.castLE hk, Fin.castLE_injective hk⟩ : Fin (k + 1) ↪ Fin n),
      f l = ∑ l : Fin (k + 1), f (Fin.castLE hk l) := Finset.sum_map _ _ _
  rw [← hmap]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  apply hf
  intro hlt
  apply hl
  rw [Finset.mem_map]
  exact ⟨⟨l, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩

theorem mul_cM {k : ℕ} (hk : k + 1 ≤ n) (g : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j : Fin n, k + 1 ≤ (i : ℕ) → g i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (x : Fin (k + 1) → F) :
    g * cM n k x = cM n k ((g.submatrix (Fin.castLE hk) (Fin.castLE hk)) *ᵥ x) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hj : (j : ℕ) = k + 1
  · by_cases hi : (i : ℕ) < k + 1
    · rw [cM_apply_pos k _ hj hi,
        sum_castLE hk (fun l => g i l * cM n k x l j)
          (fun l hl => by rw [cM_apply_neg k x (fun h => hl h.2), mul_zero])]
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      apply Finset.sum_congr rfl
      intro l _
      rw [cM_apply_pos k x hj l.2]
      rfl
    · rw [cM_apply_neg k _ (fun h => hi h.2)]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : (l : ℕ) < k + 1
      · rw [hM i l (by omega), Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega)), zero_mul]
      · rw [cM_apply_neg k x (fun h => hl h.2), mul_zero]
  · rw [cM_apply_neg k _ (fun h => hj h.1)]
    apply Finset.sum_eq_zero
    intro l _
    rw [cM_apply_neg k x (fun h => hj h.1), mul_zero]

theorem cM_mul_row {k : ℕ} (hk : k + 1 < n) (g : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j : Fin n, k + 1 ≤ (i : ℕ) → g i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (y : Fin (k + 1) → F) : cM n k y * g = cM n k y := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨k + 1, hk⟩ : Fin n)]
  · rw [hM _ j (le_refl _)]
    by_cases hj : j = ⟨k + 1, hk⟩
    · subst hj
      rw [Matrix.one_apply_eq, mul_one]
    · rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero,
        cM_apply_neg k y (fun h => hj (Fin.ext h.1))]
  · intro l _ hl
    rw [cM_apply_neg k y (fun h => hl (Fin.ext h.1)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem conj_col {k : ℕ} (hk : k + 1 < n) (g : GL (Fin n) F)
    (hM : ∀ i j : Fin n, k + 1 ≤ (i : ℕ) →
      (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j)
    (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (ht : t = (g : Matrix (Fin n) (Fin n) F).submatrix (Fin.castLE hk.le) (Fin.castLE hk.le))
    (x : Fin (k + 1) → F) : g * col n k x = col n k (t *ᵥ x) * g := by
  subst ht
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, col_coe, col_coe, mul_add, add_mul, mul_one, one_mul,
    mul_cM hk.le _ hM x, cM_mul_row hk _ hM]

def extM {k : ℕ} (n : ℕ) (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if h : (i : ℕ) < k + 1 ∧ (j : ℕ) < k + 1 then t ⟨i, h.1⟩ ⟨j, h.2⟩
    else (1 : Matrix (Fin n) (Fin n) F) i j

theorem extM_pos {k : ℕ} (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) {i j : Fin n}
    (h : (i : ℕ) < k + 1 ∧ (j : ℕ) < k + 1) : extM n t i j = t ⟨i, h.1⟩ ⟨j, h.2⟩ := by
  rw [extM, Matrix.of_apply, dif_pos h]

theorem extM_neg {k : ℕ} (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) {i j : Fin n}
    (h : ¬((i : ℕ) < k + 1 ∧ (j : ℕ) < k + 1)) :
    extM n t i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  rw [extM, Matrix.of_apply, dif_neg h]

theorem extM_submatrix {k : ℕ} (hk : k + 1 ≤ n) (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :
    (extM n t).submatrix (Fin.castLE hk) (Fin.castLE hk) = t := by
  ext i j
  rw [Matrix.submatrix_apply, extM_pos t (i := Fin.castLE hk i) (j := Fin.castLE hk j) ⟨i.2, j.2⟩]
  rfl

theorem extM_row {k : ℕ} (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (i j : Fin n)
    (hi : k + 1 ≤ (i : ℕ)) : extM n t i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  exact extM_neg t (fun h => by obtain ⟨h1, h2⟩ := h; omega)

theorem det_extM {k : ℕ} (hk : k + 1 ≤ n) (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :
    (extM n t).det = t.det := by
  rw [det_eq_submatrix hk (extM n t) (fun i j hi => extM_row t i j hi), extM_submatrix hk]

theorem exists_block {k : ℕ} (hk : k + 1 < n) (g : GL (Fin n) F) (hg : inP (k + 1) g) :
    ∃ t : GL (Fin (k + 1)) F, (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) =
        (g : Matrix (Fin n) (Fin n) F).submatrix (Fin.castLE hk.le) (Fin.castLE hk.le) ∧
      (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det = (g : Matrix (Fin n) (Fin n) F).det := by
  obtain ⟨hg1, hg2⟩ := hg
  have hd := det_eq_submatrix hk.le (g : Matrix (Fin n) (Fin n) F) hg1
  have hdet : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hdet' : ((g : Matrix (Fin n) (Fin n) F).submatrix (Fin.castLE hk.le)
      (Fin.castLE hk.le)).det ≠ 0 := by
    rw [← hd]
    exact hdet
  exact ⟨Matrix.nonsingInvUnit ((g : Matrix (Fin n) (Fin n) F).submatrix (Fin.castLE hk.le)
    (Fin.castLE hk.le)) (isUnit_iff_ne_zero.mpr hdet'), rfl, hd.symm⟩

theorem last_mulVec {k : ℕ} (hk : k + 1 < n) (g : GL (Fin n) F) (hg : inP k g)
    (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (ht : t = (g : Matrix (Fin n) (Fin n) F).submatrix (Fin.castLE hk.le) (Fin.castLE hk.le))
    (x : Fin (k + 1) → F) : (t *ᵥ x) (Fin.last k) = x (Fin.last k) := by
  subst ht
  obtain ⟨h1, _⟩ := hg
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single (Fin.last k)]
  · rw [h1 _ _ (by simp), Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rw [h1 _ _ (by simp), Matrix.one_apply_ne (fun e => hl (Fin.castLE_injective _ e).symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_ext {k : ℕ} (hk : k + 1 < n) (t : GL (Fin (k + 1)) F) :
    ∃ g : GL (Fin n) F, (g : Matrix (Fin n) (Fin n) F) =
      extM n (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) := by
  have hdet : (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hdet' : (extM n (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F)).det ≠ 0 := by
    rw [det_extM hk.le]
    exact hdet
  exact ⟨Matrix.nonsingInvUnit (extM n (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F))
    (isUnit_iff_ne_zero.mpr hdet'), rfl⟩

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem inU_col (k : ℕ) (x : Fin (k + 1) → F) : inU k (col n k x) := by
  unfold inU
  refine ⟨?_, fun i j hj => ?_⟩
  · show ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsUpperTriangular ∧
      ∀ i, ((col n k x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1
    rw [col_coe]
    exact ⟨fun i j hij => col_upper k x hij, fun i => col_diag k x i⟩
  · rw [col_coe, Matrix.add_apply, cM_apply_neg k x (fun h => by obtain ⟨h1, h2⟩ := h; omega),
      add_zero]

theorem div_extM {k : ℕ} (c : ℕ) (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F)
    (hk : k + 1 ≤ n) (h : Div c (t - 1)) : Div c (extM n t - 1) := by
  unfold PositivityTheory.JacquetShalikaLocal.Div at h ⊢
  intro i j
  by_cases h' : (i : ℕ) < k + 1 ∧ (j : ℕ) < k + 1
  · obtain ⟨y, hy, hyeq⟩ := h ⟨i, h'.1⟩ ⟨j, h'.2⟩
    refine ⟨y, hy, ?_⟩
    rw [Matrix.sub_apply, extM_pos t h', ← hyeq, Matrix.sub_apply]
    congr 1
    exact one_castLE hk ⟨i, h'.1⟩ ⟨j, h'.2⟩
  · refine ⟨0, zero_mem _, ?_⟩
    rw [Matrix.sub_apply, extM_neg t h', sub_self, mul_zero]

end Local

theorem column_mirabolic_holds : ColumnsMirabolic := by
  unfold ColumnsMirabolic ForF
  intro F _ _ _ _ _ _ μ _ ψ _ n k hk
  refine ⟨fun x y => col_add k x y, col_zero k,
    fun x => ⟨inP_col k x, inU_col k x, det_col k x, psiN_col hk ψ x⟩,
    fun g hg => inP_succ hg, fun g hg => ?_, fun t => ?_⟩
  · have hg1 : ∀ i j : Fin n, k + 1 ≤ (i : ℕ) →
        (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j := hg.1
    obtain ⟨t, ht, hdt⟩ := exists_block hk g hg
    exact ⟨t, hdt, fun x => conj_col hk g hg1 _ ht x, fun hgk x => last_mulVec hk g hgk _ ht x⟩
  · obtain ⟨g, hg⟩ := exists_ext hk t
    have hsub : (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) =
        (g : Matrix (Fin n) (Fin n) F).submatrix (Fin.castLE hk.le) (Fin.castLE hk.le) := by
      rw [hg, extM_submatrix]
    have hrow : ∀ i j : Fin n, k + 1 ≤ (i : ℕ) →
        (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
      intro i j hi
      rw [hg]
      exact extM_row _ i j hi
    have hP : inP (k + 1) g := by
      unfold inP
      refine ⟨hrow, fun i j hj => ?_⟩
      rw [hg]
      exact extM_neg _ (fun h => by obtain ⟨h1, h2⟩ := h; omega)
    refine ⟨g, hP, by rw [hg, det_extM hk.le], fun x => conj_col hk g hrow _ hsub x, ?_⟩
    intro c hc
    rw [hg]
    exact div_extM c _ hk.le hc

end GlobalTheory.CompanionTheory.JSBound

end
