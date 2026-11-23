import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescSt

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

namespace DescPf

variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

noncomputable def trT [FiniteDimensional K K₂] : K₂ ⊗[K] V →ₗ[K] V :=
  TensorProduct.lid K V ∘ₗ LinearMap.rTensor V (Algebra.trace K K₂)

lemma trT_tmul [FiniteDimensional K K₂] (x : K₂) (v : V) :
    trT (x ⊗ₜ[K] v) = Algebra.trace K K₂ x • v := by
  simp [trT]

lemma galAct_tmul (σ : K₂ ≃ₐ[K] K₂) (x : K₂) (v : V) :
    galAct σ (x ⊗ₜ[K] v) = σ x ⊗ₜ[K] v := by
  simp [galAct]

lemma sum_galAct [FiniteDimensional K K₂] [IsGalois K K₂] (y : K₂ ⊗[K] V) :
    ∑ σ : K₂ ≃ₐ[K] K₂, galAct σ y = (1 : K₂) ⊗ₜ[K] trT y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    simp only [galAct_tmul, trT_tmul]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add y z hy hz =>
    simp only [map_add, Finset.sum_add_distrib, hy, hz, TensorProduct.tmul_add]

lemma expand [FiniteDimensional K K₂] [Algebra.IsSeparable K K₂] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K K₂) (w : K₂ ⊗[K] V) :
    w = ∑ i, ((Algebra.traceForm K K₂).dualBasis
      (traceForm_nondegenerate (K := K) (L := K₂)) b i) • ((1 : K₂) ⊗ₜ[K] trT (b i • w)) := by
  set d := (Algebra.traceForm K K₂).dualBasis (traceForm_nondegenerate (K := K) (L := K₂)) b
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
    have hx : x = ∑ i, Algebra.trace K K₂ (b i * x) • d i := by
      conv_lhs => rw [← d.sum_repr x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm]
    conv_lhs => rw [hx]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, trT_tmul]
    exact TensorProduct.smul_tmul _ _ _
  | add y z hy hz =>
    simp only [smul_add, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hy, ← hz]

end DescPf

theorem galoisDescent_holds : GaloisDescentStatement := by
  intro K K₂ V _ _ _ _ _ _ _ W hW
  classical
  apply le_antisymm
  · intro w hw
    rw [DescPf.expand (Module.finBasis K K₂) w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply]
    rw [← DescPf.sum_galAct]
    exact Submodule.sum_mem _ fun σ _ => hW σ _ (W.smul_mem _ hw)
  · rw [baseSpan, Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    simpa only [SetLike.mem_coe, kPoints, Submodule.mem_comap, Submodule.restrictScalars_mem,
      TensorProduct.mk_apply] using hu

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
