import Mathlib

namespace GlobalTheory.SpanQuotientTensor

theorem span_mkQ_one_tmul {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (F : Type) [Field F] [Algebra K F] (N : Submodule F (TensorProduct K F D)) :
    Submodule.span F (Set.range (fun x : D => N.mkQ ((1 : F) ⊗ₜ[K] x))) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := N.mkQ_surjective q
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : (a ⊗ₜ[K] x : TensorProduct K F D) = a • ((1 : F) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add y z hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ hy hz

theorem main : (let d1 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (U →+* F) → Submodule F (TensorProduct LL F D) := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ ⨆ (c : U), LinearMap.range (LinearMap.baseChange F ((m : U → Module.End LL D) c) - (τ : U → F) c • LinearMap.id)); let d2 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [Algebra LL F] → (U →+* F) → Type := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ TensorProduct LL F D ⧸ d1 m F τ); let d3 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → TensorProduct LL F D →ₗ[F] d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ Submodule.mkQ (d1 m F τ)); let d4 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → D → d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (x : D) ↦ (d3 m F τ : TensorProduct LL F D → d2 m F τ) ((1 : F) ⊗ₜ[LL] x)); ∀ {LL U D : Type} [inst : Field LL] [inst_1 : Field U] [inst_2 : AddCommGroup D] [inst_3 : Module LL D] (m : U →+* Module.End LL D) (F : Type) [inst_4 : Field F] [inst_5 : Algebra LL F] (τ : U →+* F), Submodule.span F (Set.range (d4 m F τ)) = ⊤) := by
  intro d1 d2 d3 d4 LL U D _ _ _ _ m F _ _ τ
  exact span_mkQ_one_tmul F (d1 m F τ)

end GlobalTheory.SpanQuotientTensor
