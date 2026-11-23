import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def GenericPrimitive.Statement : Prop :=
  ∀ (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] (n : ℕ) (x : Fin n → L),
    IntermediateField.adjoin K (Set.range x) = ⊤ →
      ∃ D : MvPolynomial (Fin n) k, D ≠ 0 ∧ ∀ c : Fin n → k, MvPolynomial.eval c D ≠ 0 →
        IntermediateField.adjoin K {∑ j, c j • x j} = ⊤

theorem adjoin_real_I : IntermediateField.adjoin ℝ {Complex.I} = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  rw [← Complex.re_add_im z]
  have hI := IntermediateField.mem_adjoin_simple_self ℝ Complex.I
  have hre : (z.re : ℂ) ∈ IntermediateField.adjoin ℝ {Complex.I} :=
    IntermediateField.algebraMap_mem _ z.re
  have him : (z.im : ℂ) ∈ IntermediateField.adjoin ℝ {Complex.I} :=
    IntermediateField.algebraMap_mem _ z.im
  exact add_mem hre (mul_mem him hI)

theorem GenericPrimitive.hypotheses_inhabited :
    IsScalarTower ℚ ℝ ℂ ∧ FiniteDimensional ℝ ℂ ∧ Algebra.IsSeparable ℝ ℂ ∧
      IntermediateField.adjoin ℝ (Set.range ![Complex.I]) = ⊤ := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  exact adjoin_real_I

end

end GroundTheory.Heights₂.Heights.ComplexSets
