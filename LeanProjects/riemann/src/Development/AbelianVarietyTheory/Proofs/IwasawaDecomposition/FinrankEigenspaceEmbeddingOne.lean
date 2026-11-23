import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory
namespace EigenSplit

section RankOne

variable {E : Type} [Field E] [NumberField E] {K : Type} [CommRing K]

theorem baseChangeAction_toModuleEnd_apply (a : 𝓞 E) (x : K ⊗[ℤ] 𝓞 E) :
    baseChangeAction K (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E)) a x
      = (1 ⊗ₜ a) * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]

theorem tensorAction_baseChangeAction_toModuleEnd (t x : K ⊗[ℤ] 𝓞 E) :
    tensorAction (baseChangeAction K
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) t x = t * x := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    rw [tensorAction_tmul, baseChangeAction_toModuleEnd_apply, ← smul_mul_assoc,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add s t hs ht => simp [add_mul, hs, ht]

variable {ι : Type} [DecidableEq ι] {τ : ι → 𝓞 E →+* K}

theorem idem_ne_zero [Nontrivial K] (h : IsSplitting τ) (i : ι) : idem h i ≠ 0 := by
  intro h0
  have := congrFun (splitMap_idem h i) i
  rw [h0, map_zero] at this
  simp at this

theorem eigenSub_toModuleEnd_eq_span (h : IsSplitting τ) (i : ι) :
    eigenSub (baseChangeAction K (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E)))
      (τ i) = Submodule.span K {idem h i} := by
  apply le_antisymm
  · intro x hx
    have h1 := tensorAction_of_mem (σ := τ) hx (idem h i)
    rw [tensorAction_baseChangeAction_toModuleEnd, splitMap_idem, Pi.single_eq_same, one_smul,
      mul_comm, mul_idem] at h1
    rw [← h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact mem_eigenSub.2 fun a => by rw [baseChangeAction_toModuleEnd_apply, one_tmul_mul_idem]

end RankOne

theorem finrank_eigenSub_toModuleEnd_eq_one_of_isSplitting {E V : Type} [Field E] [NumberField E]
    [CommRing V] [IsDomain V] [ValuationRing V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : ι → 𝓞 E →+* V) (K : Type) [Field K] [Algebra V K] [IsFractionRing V K]
    (h : IsSplitting fun i => (algebraMap V K).comp (σ i)) (i₀ : ι) :
    Module.finrank V (eigenSub (baseChangeAction V
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  have : FaithfulSMul V K :=
    (faithfulSMul_iff_algebraMap_injective V K).2 (IsFractionRing.injective V K)
  have : Module.Flat V K := flat_of_valuationRing V K
  rw [← finrank_eigenSub_of_flat (R' := K) (extendTensor_equivariant V K _)
    (isBaseChange_extendTensor ℤ V K (𝓞 E)) (σ i₀)]
  have hs := eigenSub_toModuleEnd_eq_span h i₀
  beta_reduce at hs
  rw [hs]
  exact finrank_span_singleton (idem_ne_zero h i₀)

theorem finrank_eigenSub_toModuleEnd_eq_one {E V : Type} [Field E] [NumberField E] [CommRing V]
    [IsDomain V] [ValuationRing V] [CharZero V]
    {ι : Type} [Fintype ι] (σ : ι → 𝓞 E →+* V) (hσ : Function.Injective σ)
    (hc : Fintype.card ι = Module.finrank ℚ E) (i₀ : ι) :
    Module.finrank V (eigenSub (baseChangeAction V
      (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  classical
  exact finrank_eigenSub_toModuleEnd_eq_one_of_isSplitting σ (FractionRing V)
    (isSplitting_fractionRing hσ hc) i₀

end EigenSplit
end GlobalTheory
