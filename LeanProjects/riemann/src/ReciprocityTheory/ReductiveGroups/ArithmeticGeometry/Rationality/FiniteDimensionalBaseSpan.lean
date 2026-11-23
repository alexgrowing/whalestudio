import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDetectStatement

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def incU (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    F ⊗[K] U →ₗ[F] F ⊗[K] V :=
  AlgebraTensorModule.map (LinearMap.id : F →ₗ[F] F) U.subtype

theorem incU_apply_eq_lTensor (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (y : F ⊗[K] U) : incU F U y = LinearMap.lTensor F U.subtype y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp [incU]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem baseSpan_eq_range (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    baseSpan F U = LinearMap.range (incU F U) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(1 : F) ⊗ₜ[K] (⟨u, hu⟩ : U), by simp [incU]⟩
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      have : incU F U (a ⊗ₜ[K] u) = a • ((1 : F) ⊗ₜ[K] (u : V)) := by
        simp [incU, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, u.2, rfl⟩)
    | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

theorem mem_baseSpan_iff (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (x : F ⊗[K] V) : x ∈ baseSpan F U ↔ LinearMap.lTensor F U.mkQ x = 0 := by
  have hex := lTensor_exact F (LinearMap.exact_subtype_mkQ U) (Submodule.mkQ_surjective U)
  rw [hex x, baseSpan_eq_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, (incU_apply_eq_lTensor F U y).symm⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, incU_apply_eq_lTensor F U y⟩

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

noncomputable def fldIncl (K₁ : IntermediateField K Ω) : K₁ →ₗ[K] Ω :=
  (IsScalarTower.toAlgHom K K₁ Ω).toLinearMap

theorem fldIncl_injective (K₁ : IntermediateField K Ω) : Function.Injective (fldIncl K₁) :=
  (algebraMap K₁ Ω).injective

theorem inclT_tmul' (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) ⊗ₜ[K] v := rfl

theorem lTensor_mkQ_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V) :
    LinearMap.lTensor Ω U.mkQ (inclT K₁ V x) =
      LinearMap.rTensor (V ⧸ U) (fldIncl K₁) (LinearMap.lTensor K₁ U.mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [inclT_tmul', fldIncl]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem mem_baseSpan_of_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : inclT K₁ V x ∈ baseSpan Ω U) : x ∈ baseSpan K₁ U := by
  rw [mem_baseSpan_iff] at h ⊢
  rw [lTensor_mkQ_inclT] at h
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := V ⧸ U) _ (fldIncl_injective K₁)
  rw [h, map_zero]

theorem inclT_mem_baseSpan (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : x ∈ baseSpan K₁ U) : inclT K₁ V x ∈ baseSpan Ω U := by
  rw [mem_baseSpan_iff] at h ⊢
  rw [lTensor_mkQ_inclT, h, map_zero]

theorem inclT_tmul (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) • ((1 : Ω) ⊗ₜ[K] v) := by
  rw [inclT_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem definedOver_iff (c : Module.Dual Ω (Ω ⊗[K] V)) (K' : IntermediateField K Ω) :
    DefinedOver c K' ↔ ∀ v : V, c ((1 : Ω) ⊗ₜ[K] v) ∈ K' := by
  constructor
  · intro h v
    obtain ⟨y, hy⟩ := h ((1 : K') ⊗ₜ[K] v)
    rw [inclT_tmul] at hy
    simp only [OneMemClass.coe_one, one_smul] at hy
    rw [← hy]; exact y.2
  · intro h x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a v =>
      refine ⟨a * ⟨_, h v⟩, ?_⟩
      rw [inclT_tmul, map_smul, smul_eq_mul]
      simp
    | add y z hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩

theorem DefinedOver.mono {c : Module.Dual Ω (Ω ⊗[K] V)} {K' K₁ : IntermediateField K Ω}
    (h : DefinedOver c K') (hle : K' ≤ K₁) : DefinedOver c K₁ := by
  rw [definedOver_iff] at h ⊢
  exact fun v => hle (h v)

theorem incU_injective (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Function.Injective (incU F U) := by
  intro x y h
  rw [incU_apply_eq_lTensor, incU_apply_eq_lTensor] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) U.subtype U.injective_subtype h

theorem finrank_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : Module.finrank F (baseSpan F U) = Module.finrank K U := by
  rw [baseSpan_eq_range, LinearMap.finrank_range_of_inj (incU_injective F U),
    Module.finrank_baseChange]

theorem finiteDimensional_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : FiniteDimensional F (baseSpan F U) := by
  rw [baseSpan_eq_range]; infer_instance

theorem exists_ratFun {c : Module.Dual Ω (Ω ⊗[K] V)} {K₁ : IntermediateField K Ω}
    (h : DefinedOver c K₁) :
    ∃ φ : Module.Dual K₁ (K₁ ⊗[K] V), ∀ x, algebraMap K₁ Ω (φ x) = c (inclT K₁ V x) := by
  let ψ : K₁ ⊗[K] V →ₗ[K₁] Ω := (c.restrictScalars K₁).comp (inclT K₁ V)
  have hr : ∀ x, ψ x ∈ LinearMap.range (Algebra.linearMap K₁ Ω) := fun x => by
    obtain ⟨y, hy⟩ := h x; exact ⟨y, hy⟩
  let e := LinearEquiv.ofInjective (Algebra.linearMap K₁ Ω) (algebraMap K₁ Ω).injective
  refine ⟨e.symm.toLinearMap ∘ₗ ψ.codRestrict _ hr, fun x => ?_⟩
  have h1 : ((e (e.symm ⟨ψ x, hr x⟩) : LinearMap.range (Algebra.linearMap K₁ Ω)) : Ω) = ψ x := by
    rw [e.apply_symm_apply]
  exact h1

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
