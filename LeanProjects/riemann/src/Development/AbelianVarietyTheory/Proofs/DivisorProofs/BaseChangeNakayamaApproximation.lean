import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
open GlobalTheory.RingChain
open scoped TensorProduct Pointwise ChangeOfRings

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RingChain

theorem modIso_tensor_mod : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (a : A) (g : R), algebraMap A R a = g →
    ModIso R a → ∀ (M M' : Type) [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module R M']
    (e : R ⊗[A] M ≃ₗ[R] M'), (∀ z : M', ∃ y : M, z - e (1 ⊗ₜ y) ∈ g • (⊤ : Submodule R M')) ∧
      ∀ y : M, e (1 ⊗ₜ y) ∈ g • (⊤ : Submodule R M') → y ∈ a • (⊤ : Submodule A M) := by
  intro A R _ _ _ a g hg hM M M' _ _ _ _ e
  subst hg
  refine ⟨fun z => ?_, fun y hy => ?_⟩
  · have key : ∀ t : R ⊗[A] M, ∃ y : M, t - 1 ⊗ₜ y ∈ algebraMap A R a • (⊤ : Submodule R (R ⊗[A] M)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add s t hs ht =>
        obtain ⟨y, hy⟩ := hs
        obtain ⟨y', hy'⟩ := ht
        refine ⟨y + y', ?_⟩
        have := Submodule.add_mem _ hy hy'
        convert this using 1
        rw [TensorProduct.tmul_add]; abel
      | tmul r m =>
        obtain ⟨x, c, hc⟩ := hM.1 r
        refine ⟨x • m, ?_⟩
        have : r ⊗ₜ[A] m - (1 : R) ⊗ₜ (x • m) = algebraMap A R a • (c ⊗ₜ m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, ← hc, TensorProduct.sub_tmul, ← TensorProduct.smul_tmul,
            Algebra.algebraMap_eq_smul_one]
        rw [this]
        exact Submodule.smul_mem_pointwise_smul _ _ _ trivial
    obtain ⟨y, hy⟩ := key (e.symm z)
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    refine ⟨y, ?_⟩
    have : z - e (1 ⊗ₜ y) = algebraMap A R a • e w := by
      rw [← map_smul, hw, map_sub, LinearEquiv.apply_symm_apply]
    rw [this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ trivial
  · let φ : A ⧸ Ideal.span {a} →+* R ⧸ Ideal.span {algebraMap A R a} :=
      Ideal.quotientMap _ (algebraMap A R) (Ideal.span_le.2 (by
        rintro _ rfl
        exact Ideal.mem_span_singleton_self _))
    have hφ : ∀ x, φ (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap A R x) := fun _ => rfl
    have bij : Function.Bijective φ := by
      refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun r => ?_⟩
      · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [hφ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hM.2 x hx))
      · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨x, hx⟩ := hM.1 r
        refine ⟨Ideal.Quotient.mk _ x, ?_⟩
        rw [hφ, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact hx
    let ε := RingEquiv.ofBijective φ bij
    let τ : R →+* A ⧸ Ideal.span {a} := ε.symm.toRingHom.comp (Ideal.Quotient.mk _)
    have hτ : ∀ x, τ (algebraMap A R x) = Ideal.Quotient.mk _ x := fun x =>
      ε.symm_apply_eq.2 (hφ x).symm
    have hτa : τ (algebraMap A R a) = 0 := by
      rw [hτ]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)
    let τA : R →ₗ[A] A ⧸ Ideal.span {a} :=
      { toFun := τ
        map_add' := map_add τ
        map_smul' := fun c r => by
          rw [Algebra.smul_def, map_mul, hτ, RingHom.id_apply, Algebra.smul_def]; rfl }
    have h0 : ∀ t : R ⊗[A] M, τA.rTensor M (algebraMap A R a • t) = 0 := fun t => by
      induction t using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero]
      | add s t hs ht => rw [smul_add, map_add, hs, ht, add_zero]
      | tmul r m =>
        rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul]
        change τ (algebraMap A R a * r) ⊗ₜ[A] m = 0
        rw [map_mul, hτa, zero_mul, TensorProduct.zero_tmul]
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    have h1 : (1 : R) ⊗ₜ[A] y = algebraMap A R a • e.symm w := by
      apply e.injective
      rw [map_smul, LinearEquiv.apply_symm_apply, hw]
    have h2 : (Ideal.Quotient.mk (Ideal.span {a}) 1) ⊗ₜ[A] y = 0 := by
      have := h0 (e.symm w)
      rw [← h1, LinearMap.rTensor_tmul] at this
      rw [← this]
      change _ = τ 1 ⊗ₜ[A] y
      rw [map_one, map_one]
    have h3 := congrArg (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {a})) h2
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero, one_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.ideal_span_singleton_smul] at h3
    exact h3

end GlobalTheory.RingChain
