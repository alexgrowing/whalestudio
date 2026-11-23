import Mathlib

theorem UpperTheory.Reformulated.B.AlternatingSumZero.alt_sum_zero.{u_1} :
    ∀ {A : Type u_1} [inst : AddCommGroup A] {n : ℕ}
      (G : ({ len := n : SimplexCategory } ⟶ { len := n + (2 : ℕ) : SimplexCategory }) → A),
      ∑ i : Fin (n + (3 : ℕ)),
          ∑ j : Fin (n + (2 : ℕ)),
            ((-1 : ℤ) ^ (↑i : ℕ) * (-1 : ℤ) ^ (↑j : ℕ)) •
              G (CategoryTheory.CategoryStruct.comp (SimplexCategory.δ j) (SimplexCategory.δ i)) =
        (0 : A) := by
  intro A _ n G
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Fin (n + 3) × Fin (n + 2) => (p.1 : ℕ) ≤ (p.2 : ℕ)), add_eq_zero_iff_eq_neg,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun p hp => (p.2.succ, p.1.castLT
      (lt_of_le_of_lt (Finset.mem_filter.mp hp).2 p.2.isLt))) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    have h := (Finset.mem_filter.mp hp).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, Fin.val_castLT] at h ⊢
    omega
  · rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ h
    simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castLT] at h ⊢
    omega
  · rintro ⟨i, j⟩ hp
    have h := (Finset.mem_filter.mp hp).2
    have hi := i.isLt
    simp only [not_le] at h
    refine ⟨(j.castSucc, ⟨i.val - 1, by omega⟩), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]
      omega
    · simp only [Prod.mk.injEq, Fin.ext_iff, Fin.val_succ, Fin.val_castLT, Fin.val_castSucc,
        and_true]
      omega
  · rintro ⟨i, j⟩ hp
    have h : (i : ℕ) ≤ (j : ℕ) := (Finset.mem_filter.mp hp).2
    have hi : (i : ℕ) < n + 2 := lt_of_le_of_lt h j.isLt
    have key := SimplexCategory.δ_comp_δ (i := i.castLT hi) (j := j) h
    rw [Fin.castSucc_castLT] at key
    dsimp only
    rw [key, ← neg_smul]
    congr 1
    simp only [Fin.val_succ, Fin.val_castLT]
    ring
