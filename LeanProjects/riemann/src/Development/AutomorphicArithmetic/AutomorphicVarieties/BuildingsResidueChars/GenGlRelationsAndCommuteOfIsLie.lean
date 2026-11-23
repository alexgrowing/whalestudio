import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem single_comm {R : Type} [CommRing R] {n : ℕ} (i j k m : Fin n) (x y : R) :
    (Matrix.single i j x * Matrix.single k m y : Matrix (Fin n) (Fin n) R) =
      if j = k then Matrix.single i m (x * y) else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.single_mul_single_same _ _ _ _ _
  · ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hj : j = t
    · subst hj
      simp only [Ne.symm h, false_and, if_false, mul_zero]
    · simp [hj]

private theorem unitMap_comm {R : Type} [CommRing R] [Algebra ℝ R] {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]
    [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (hl : IsLie l) (i j k m : Fin n)
    (a b : ℂ ⊗[ℝ] R) :
    unitMap l i j a * unitMap l k m b - unitMap l k m b * unitMap l i j a =
      (if j = k then unitMap l i m (a * b) else 0) - (if m = i then unitMap l k j (a * b) else 0) := by
  have hmain : ∀ (c d : ℂ) (x y : R),
      unitMap l i j (c ⊗ₜ x) * unitMap l k m (d ⊗ₜ y) - unitMap l k m (d ⊗ₜ y) * unitMap l i j (c ⊗ₜ x) =
        (if j = k then unitMap l i m ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) -
          (if m = i then unitMap l k j ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) := by
    intro c d x y
    simp only [unitMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, smul_mul_smul_comm]
    rw [mul_comm d c, ← smul_sub, hl, single_comm, single_comm, mul_comm y x]
    split_ifs <;> simp [map_sub, smul_sub]
  rw [← sub_eq_zero]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul d y => rw [sub_eq_zero]; exact hmain c d x y
    | add b₁ b₂ h₁ h₂ =>
      have h := congrArg₂ (· + ·) h₁ h₂
      simp only [add_zero] at h
      refine Eq.trans ?_ h
      split_ifs <;> simp only [map_add, mul_add, add_mul] <;> abel
  | add a₁ a₂ h₁ h₂ =>
    have h := congrArg₂ (· + ·) h₁ h₂
    simp only [add_zero] at h
    refine Eq.trans ?_ h
    split_ifs <;> simp only [map_add, mul_add, add_mul] <;> abel

theorem UpperTheory.gen_glRelations_and_commute_of_isLie :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A), IsLie l → (∀ τ, Formalism.REAL.GlRel (gen D l τ)) ∧ ∀ τ σ, τ ≠ σ → ∀ i j k m, Commute (gen D l τ i j) (gen D l σ k m) := by
  intro R _ _ ι _ n A _ _ _ _ D l hl
  have idem : ∀ τ, D.e τ * D.e τ = D.e τ := by
    intro τ
    calc D.e τ * D.e τ = D.e τ * ∑ σ, D.e σ := by
          rw [Finset.mul_sum, Finset.sum_eq_single τ]
          · intro σ _ h
            exact D.orth τ σ (Ne.symm h)
          · simp
      _ = D.e τ := by rw [D.sum, mul_one]
  refine ⟨fun τ => ?_, fun τ σ h i j k m => ?_⟩
  · intro a b c d
    simp only [gen]
    rw [unitMap_comm l hl, idem]
  · unfold Commute SemiconjBy
    rw [← sub_eq_zero]
    simp only [gen]
    rw [unitMap_comm l hl, D.orth τ σ h]
    simp
