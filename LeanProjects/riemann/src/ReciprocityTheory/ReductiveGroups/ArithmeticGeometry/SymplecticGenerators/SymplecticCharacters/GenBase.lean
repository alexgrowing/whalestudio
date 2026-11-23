import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement

open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

abbrev spH (g : ℕ) : Submonoid (Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) :=
  Submonoid.closure (spGens g)

theorem spTransl_mem {S : Matrix (Fin g) (Fin g) ℤ} (hS : S.IsSymm) : spTransl S ∈ spH g := Submonoid.subset_closure (Set.mem_union_left _ (Set.mem_union_left _ ⟨S, hS, rfl⟩))

theorem spDiag_mem (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : spDiag U ∈ spH g := Submonoid.subset_closure (Set.mem_union_left _ (Set.mem_union_right _ ⟨U, rfl⟩))

theorem J_mem_spH : J (Fin g) ℤ ∈ spH g := Submonoid.subset_closure (Set.mem_union_right _ (Set.mem_singleton _))

theorem spTransl_neg_mul (S : Matrix (Fin g) (Fin g) ℤ) : spTransl (-S) * spTransl S = 1 := by

  simp [spTransl, fromBlocks_multiply, fromBlocks_one]

theorem spDiag_inv_mul (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : spDiag U⁻¹ * spDiag U = 1 := by

  simp [spDiag, fromBlocks_multiply, ← Matrix.transpose_mul, fromBlocks_one]

theorem J_cube : J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ = -J (Fin g) ℤ := by

  rw [Matrix.J_squared, neg_mul, one_mul]

theorem J_pow_four : J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ = 1 := by

  rw [J_cube, neg_mul, Matrix.J_squared, neg_neg]

theorem spH_exists_inv {x : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hx : x ∈ spH g) :
    ∃ y ∈ spH g, y * x = 1 := by

  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ
    · have hS' : (-S).IsSymm := by
        unfold Matrix.IsSymm at hS ⊢
        rw [Matrix.transpose_neg, hS]
      exact ⟨spTransl (-S), spTransl_mem hS', spTransl_neg_mul S⟩
    · exact ⟨spDiag U⁻¹, spDiag_mem _, spDiag_inv_mul U⟩
    · rw [Set.mem_singleton_iff] at hJ
      subst hJ
      exact ⟨J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ, mul_mem (mul_mem J_mem_spH J_mem_spH) J_mem_spH, J_pow_four⟩
  | one => exact ⟨1, one_mem _, one_mul 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'm, hx'⟩ := hx
    obtain ⟨y', hy'm, hy'⟩ := hy
    refine ⟨y' * x', mul_mem hy'm hx'm, ?_⟩
    rw [mul_assoc, ← mul_assoc x' x y, hx', one_mul, hy']

theorem mem_spH_of_mul_eq_one {M N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hN : N ∈ spH g)
    (h : N * M = 1) : M ∈ spH g := by

  obtain ⟨y, hy, hyN⟩ := spH_exists_inv hN
  have h1 : M = y := by
    calc M = (y * N) * M := by rw [hyN, one_mul]
      _ = y * (N * M) := mul_assoc _ _ _
      _ = y := by rw [h, mul_one]
  rw [h1]
  exact hy

theorem spTransl_mem_sp {S : Matrix (Fin g) (Fin g) ℤ} (hS : S.IsSymm) :
    spTransl S ∈ symplecticGroup (Fin g) ℤ := by

  rw [SymplecticGroup.mem_iff]
  have hS' : Sᵀ = S := hS
  unfold spTransl
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hS']

theorem spDiag_mem_sp (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) : spDiag U ∈ symplecticGroup (Fin g) ℤ := by

  rw [SymplecticGroup.mem_iff]
  unfold spDiag
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [← Matrix.transpose_mul]

theorem spGens_subset (g : ℕ) : spGens g ⊆ symplecticGroup (Fin g) ℤ := by

  intro x hx
  rcases hx with (⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ
  · exact spTransl_mem_sp hS
  · exact spDiag_mem_sp U
  · rw [Set.mem_singleton_iff] at hJ
    subst hJ
    exact SymplecticGroup.J_mem _ _

theorem spH_le (g : ℕ) : spH g ≤ symplecticGroup (Fin g) ℤ := Submonoid.closure_le.mpr (spGens_subset g)

def spLow (S : Matrix (Fin g) (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks 1 0 S 1

theorem spLow_eq (S : Matrix (Fin g) (Fin g) ℤ) :
    spLow S = J (Fin g) ℤ * spTransl (-S) * (J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ) := by

  rw [J_cube]
  unfold spLow spTransl
  rw [Matrix.J, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem spLow_mem {S : Matrix (Fin g) (Fin g) ℤ} (hS : S.IsSymm) : spLow S ∈ spH g := by

  have hS' : (-S).IsSymm := by
    unfold Matrix.IsSymm at hS ⊢
    rw [Matrix.transpose_neg, hS]
  rw [spLow_eq]
  exact mul_mem (mul_mem J_mem_spH (spTransl_mem hS')) (mul_mem (mul_mem J_mem_spH J_mem_spH) J_mem_spH)

abbrev eJ (j : Fin g) : Matrix (Fin g) (Fin g) ℤ := single j j 1

theorem eJ_symm (j : Fin g) : (eJ j).IsSymm := by

  show (single j j (1 : ℤ))ᵀ = single j j 1
  rw [Matrix.transpose_single]

theorem eJ_mul_self (j : Fin g) : eJ j * eJ j = eJ j := by

  simp [eJ, Matrix.single_mul_single_same]

def spPJ (j : Fin g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ :=
  fromBlocks (1 - eJ j) (eJ j) (-eJ j) (1 - eJ j)

theorem spPJ_eq (j : Fin g) : spPJ j = spTransl (eJ j) * spLow (-eJ j) * spTransl (eJ j) := by

  have hE := eJ_mul_self j
  unfold spPJ spTransl spLow
  rw [fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, hE] <;> abel

theorem spPJ_mem (j : Fin g) : spPJ j ∈ spH g := by

  have hE := eJ_symm j
  have hE' : (-eJ j).IsSymm := by
    unfold Matrix.IsSymm at hE ⊢
    rw [Matrix.transpose_neg, hE]
  rw [spPJ_eq]
  exact mul_mem (mul_mem (spTransl_mem hE) (spLow_mem hE')) (spTransl_mem hE)

theorem fromBlocks_mul_inl (A B C D : Matrix (Fin g) (Fin g) ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (fromBlocks A B C D * M) (Sum.inl i) p =
      (∑ j, A i j * M (Sum.inl j) p) + ∑ j, B i j * M (Sum.inr j) p := by

  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem fromBlocks_mul_inr (A B C D : Matrix (Fin g) (Fin g) ℤ)
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (i : Fin g) (p : Fin g ⊕ Fin g) :
    (fromBlocks A B C D * M) (Sum.inr i) p =
      (∑ j, C i j * M (Sum.inl j) p) + ∑ j, D i j * M (Sum.inr j) p := by

  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem mul_col_of_unit {M O : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} {p : Fin g ⊕ Fin g}
    (h : ∀ r, M r p = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r p) (q : Fin g ⊕ Fin g) :
    (O * M) q p = O q p := by

  rw [Matrix.mul_apply]
  simp_rw [h]
  simp [Matrix.one_apply]

theorem row_inr_of_col_inl {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {i : Fin g}
    (h : ∀ r, M r (Sum.inl i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl i))
    (q : Fin g ⊕ Fin g) :
    M (Sum.inr i) q = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr i) q := by

  have h1 : Mᵀ * J (Fin g) ℤ * M = J (Fin g) ℤ := SymplecticGroup.mem_iff'.mp hM
  have h2 := congrFun (congrFun h1 q) (Sum.inl i)
  rw [mul_col_of_unit h, Matrix.mul_apply] at h2
  have hJ : ∀ r, J (Fin g) ℤ r (Sum.inl i) = if r = Sum.inr i then 1 else 0 := by
    intro r
    rcases r with r | r <;> by_cases hri : r = i <;> simp [Matrix.J, Matrix.one_apply, hri]
  simp_rw [hJ, Matrix.transpose_apply] at h2
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [h2, Matrix.one_apply]
  by_cases hq : q = Sum.inr i
  · subst hq
    simp
  · rw [if_neg hq, if_neg (Ne.symm hq)]

theorem row_inl_of_col_inr {M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hM : M ∈ symplecticGroup (Fin g) ℤ) {i : Fin g}
    (h : ∀ r, M r (Sum.inr i) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr i))
    (q : Fin g ⊕ Fin g) :
    M (Sum.inl i) q = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inl i) q := by

  have h1 : Mᵀ * J (Fin g) ℤ * M = J (Fin g) ℤ := SymplecticGroup.mem_iff'.mp hM
  have h2 := congrFun (congrFun h1 q) (Sum.inr i)
  rw [mul_col_of_unit h, Matrix.mul_apply] at h2
  have hJ : ∀ r, J (Fin g) ℤ r (Sum.inr i) = if r = Sum.inl i then -1 else 0 := by
    intro r
    rcases r with r | r <;> by_cases hri : r = i <;> simp [Matrix.J, Matrix.one_apply, hri]
  simp_rw [hJ, Matrix.transpose_apply] at h2
  simp only [mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  rw [Matrix.one_apply]
  by_cases hq : q = Sum.inl i
  · subst hq
    rw [if_pos rfl] at h2
    simp only [if_true]
    linarith
  · rw [if_neg hq] at h2
    rw [if_neg (Ne.symm hq)]
    linarith

end ReciprocityTheory.ChartRestriction.G.Key.Chi
