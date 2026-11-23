import Mathlib

theorem UpperTheory.isOpenEmbedding_units_val_generalLinearPi :
    ∀ (W : Type) [Finite W] (K : W → Type) [∀ w, NontriviallyNormedField (K w)] (n : ℕ), Topology.IsOpenEmbedding (Units.val : GL (Fin n) (∀ w, K w) → Matrix (Fin n) (Fin n) (∀ w, K w)) := by
  intro W _ K _ n
  have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) (∀ w, K w) => M.det) :=
    continuous_id.matrix_det
  have hadj : Continuous (fun M : Matrix (Fin n) (Fin n) (∀ w, K w) => M.adjugate) :=
    continuous_id.matrix_adjugate
  have hU : ∀ M : Matrix (Fin n) (Fin n) (∀ w, K w), IsUnit M ↔ ∀ w, M.det w ≠ 0 := by
    intro M
    rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
    simp only [isUnit_iff_ne_zero]
  refine ⟨?_, ?_⟩
  · refine Units.isEmbedding_val_mk'
      (f := fun M : Matrix (Fin n) (Fin n) (∀ w, K w) =>
        (fun w => (M.det w)⁻¹ : ∀ w, K w) • M.adjugate) ?_ ?_
    · have h1 : ContinuousOn (fun M : Matrix (Fin n) (Fin n) (∀ w, K w) =>
          (fun w => (M.det w)⁻¹ : ∀ w, K w)) {x | IsUnit x} := by
        refine continuousOn_pi.2 fun w => ?_
        exact (((continuous_apply w).comp hdet).continuousOn).inv₀ fun M hM => (hU M).1 hM w
      refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
      exact h1.mul (hadj.matrix_elem i j).continuousOn
    · intro u
      have hu := (hU u.1).1 u.isUnit
      symm
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
      have : ((fun w => ((u.1).det w)⁻¹ : ∀ w, K w) * (u.1).det) = 1 := by
        funext w
        exact inv_mul_cancel₀ (hu w)
      rw [this, one_smul]
  · have : Set.range (Units.val : GL (Fin n) (∀ w, K w) → Matrix (Fin n) (Fin n) (∀ w, K w))
        = ⋂ w, {M : Matrix (Fin n) (Fin n) (∀ w, K w) | M.det w ≠ 0} := by
      ext M
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      exact hU M
    rw [this]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_ne_fun ((continuous_apply w).comp hdet) continuous_const
