import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBUnitary

noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} {i₀ : Fin n} {em : Fin k → Fin n}

theorem cB_dM (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z x y : R) (hxy : x * y = 1) :
    cB i₀ em u v z * dM i₀ x y = dM i₀ x y * cB i₀ em (fun j => y * u j) (fun j => y * v j) (y * y * z) := by
  have hS : ∀ (w : Fin k → R) a b, (∑ j, Matrix.single i₀ (em j) (w j)) a b =
      if a = i₀ then ∑ j, (if em j = b then w j else 0) else 0 := by
    intro w a b
    rw [Matrix.sum_apply]
    split_ifs with ha
    · subst ha; exact Finset.sum_congr rfl fun j _ => by rw [Matrix.single_apply]; simp
    · exact Finset.sum_eq_zero fun j _ => by
        rw [Matrix.single_apply]; split_ifs with h
        · exact absurd h.1.symm ha
        · rfl
  have hT : ∀ (w : Fin k → R) a b, (∑ j, Matrix.single (em j) i₀ (w j)) a b =
      if b = i₀ then ∑ j, (if em j = a then w j else 0) else 0 := by
    intro w a b
    rw [Matrix.sum_apply]
    split_ifs with hb
    · subst hb; exact Finset.sum_congr rfl fun j _ => by rw [Matrix.single_apply]; simp
    · exact Finset.sum_eq_zero fun j _ => by
        rw [Matrix.single_apply]; split_ifs with h
        · exact absurd h.2.symm hb
        · rfl
  have hs0 : ∀ (w : Fin k → R), ∑ j, (if em j = i₀ then w j else 0) = 0 :=
    fun w => Finset.sum_eq_zero fun j _ => by rw [if_neg (hem j)]
  have hsy : ∀ (w : Fin k → R) b, ∑ j, (if em j = b then y * w j else 0) = y * ∑ j, (if em j = b then w j else 0) := by
    intro w b; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [dM_eq_diag]
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases p with a | a <;> rcases q with b | b
  · simp only [cB, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.one_apply, hS, hsy, dg, Sum.inl.injEq, reduceCtorEq,
      if_false]
    by_cases hab : a = b
    · subst hab; by_cases ha : a = i₀
      · subst ha; simp [hs0]
      · simp [ha]
    · by_cases ha : a = i₀
      · subst ha
        simp only [if_neg hab, if_true, if_neg (Ne.symm hab), zero_add, mul_one]
        rw [← mul_assoc, hxy, one_mul]
      · simp [ha, hab]
  · simp only [cB, Matrix.fromBlocks_apply₁₂, Matrix.single_apply, dg, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false]
    by_cases h : i₀ = a ∧ i₀ = b
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true]
      linear_combination (-(y * z)) * hxy
    · simp only [if_neg h, zero_mul, mul_zero]
  · simp [cB]
  · simp only [cB, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.one_apply, hT, hsy, dg, Sum.inr.injEq, reduceCtorEq,
      if_false]
    by_cases hab : a = b
    · subst hab; by_cases ha : a = i₀
      · subst ha; simp [hs0]
      · simp [ha]
    · by_cases hb : b = i₀
      · subst hb
        simp only [if_neg hab, if_true, if_neg hab, zero_sub]
        ring
      · simp [hb, hab]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
