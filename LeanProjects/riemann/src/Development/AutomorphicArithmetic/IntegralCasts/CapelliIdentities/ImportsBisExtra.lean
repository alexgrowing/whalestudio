import Mathlib

theorem UpperTheory.Reformulated.B.DYlb5.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (f : Module.Dual k (Matrix (Fin n) (Fin n) k)), Continuous (⇑f : Matrix (Fin n) (Fin n) k → k) := by
  intro k _ _ _ _ n f
  haveI : IsTopologicalRing k := inferInstance
  have key : ∀ M : Matrix (Fin n) (Fin n) k,
      f M = ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (M i j) = (M i j) • Matrix.single i j (1 : k) := by
      simp [Matrix.smul_single]
    rw [this, map_smul, smul_eq_mul]
  have : (⇑f : Matrix (Fin n) (Fin n) k → k) =
      fun M => ∑ i, ∑ j, M i j * f (Matrix.single i j 1) := funext key
  rw [this]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).mul continuous_const
