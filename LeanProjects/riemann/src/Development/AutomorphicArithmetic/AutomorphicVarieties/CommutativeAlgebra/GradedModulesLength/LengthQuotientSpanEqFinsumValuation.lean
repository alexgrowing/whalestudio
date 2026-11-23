import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthDet
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.DedekindDomain.Instances

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped nonZeroDivisors

private theorem length_quotient_eq_norm_valuation {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type} [CommRing D] [Algebra O D] [Module.Finite O D] [Module.Free O D] (a : D) :
    Module.length O (D ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal O (Algebra.norm O a) := by
  classical
  let b := Module.Free.chooseBasis O D
  let f : D →ₗ[O] D := Algebra.lmul O D a
  let Φ := LinearMap.toMatrix b b f
  have hdet : Algebra.norm O a = Φ.det := by
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  have hmul : Φ.mulVecLin = b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := b.equivFun.surjective y
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    simp only [Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f x
  have hI : (Ideal.span {a}).restrictScalars O = LinearMap.range f := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range, f,
      Algebra.coe_lmul_eq_mul]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
  have hmap : (LinearMap.range f).map b.equivFun.toLinearMap = LinearMap.range Φ.mulVecLin := by
    rw [hmul, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ← LinearMap.range_eq_map]
  let e : (D ⧸ Ideal.span {a}) ≃ₗ[O] KStar.Selmer.H2 Φ :=
    (Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a})).symm.trans
      ((Submodule.quotEquivOfEq _ _ hI).trans (Submodule.Quotient.equiv _ _ b.equivFun hmap))
  rw [e.length_eq, hdet]
  exact KStar.Selmer.length_cokernel_eq_addVal_det Φ

private theorem algHom_finite_domain_injective {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] (σ : D →ₐ[O] K) :
    Function.Injective σ := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite O D
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : (RingHom.ker σ).comap (algebraMap O D) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).1 h,
      fun h => by simp [h]⟩
  have hmem : x ∈ RingHom.ker σ := hx
  rw [Ideal.eq_bot_of_comap_eq_bot hker] at hmem
  exact hmem

attribute [local instance] FractionRing.liftAlgebra in
private theorem algebra_norm_eq_prod_embeddings {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    {K : Type} [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] [Module.Free O D]
    (a : D) : ∃ _ : Fintype (D →ₐ[O] K), algebraMap O K (Algebra.norm O a) = ∏ σ : D →ₐ[O] K, σ a := by
  classical
  have : IsScalarTower O (FractionRing O) K := FractionRing.isScalarTower_liftAlgebra O K
  let M := Algebra.algebraMapSubmonoid D O⁰
  let L := Localization M
  have hM : M ≤ D⁰ := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O D)).2 (nonZeroDivisors.ne_zero hm))
  have : IsDomain L := IsLocalization.isDomain_localization hM
  have hF : IsField L := by
    have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
    exact isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing O))
  letI : Field L := hF.toField
  letI : Algebra (FractionRing O) L := localizationAlgebra O⁰ D
  have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
  have hN : Algebra.norm (FractionRing O) (algebraMap D L a) =
      algebraMap O (FractionRing O) (Algebra.norm O a) :=
    Algebra.norm_localization O O⁰ a
  have hE := Algebra.norm_eq_prod_embeddings (FractionRing O) K (algebraMap D L a)
  let r : (L →ₐ[FractionRing O] K) → (D →ₐ[O] K) := fun τ =>
    (τ.restrictScalars O).comp (IsScalarTower.toAlgHom O D L)
  have hinj : Function.Injective r := by
    intro τ₁ τ₂ h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext M
    ext d
    exact DFunLike.congr_fun h d
  have hsurj : Function.Surjective r := by
    intro σ
    have hu : ∀ y : M, IsUnit ((σ : D →+* K) y) := by
      rintro ⟨_, m, hm, rfl⟩
      rw [AlgHom.coe_toRingHom, AlgHom.commutes]
      exact isUnit_iff_ne_zero.2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 (nonZeroDivisors.ne_zero hm))
    let τ₀ : L →+* K := IsLocalization.lift hu
    have hc : τ₀.comp (algebraMap (FractionRing O) L) = algebraMap (FractionRing O) K := by
      apply IsLocalization.ringHom_ext O⁰
      ext c
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply O D L, IsLocalization.lift_eq]
      simp
    refine ⟨{ τ₀ with commutes' := fun x => DFunLike.congr_fun hc x }, ?_⟩
    ext d
    simp [r, τ₀, IsLocalization.lift_eq]
  letI inst : Fintype (D →ₐ[O] K) := Fintype.ofSurjective r hsurj
  refine ⟨inst, ?_⟩
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) K, ← hN, hE]
  exact Fintype.prod_bijective r ⟨hinj, hsurj⟩ _ _ (fun τ => rfl)

theorem UpperTheory.V.Alg.M.length_quotient_span_eq_finsum_valuation :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] (a : D), a ≠ 0 →
      Finite (D →ₐ[O] K) ∧ Module.length O (D ⧸ Ideal.span {a}) ≠ ⊤ ∧
      (((Module.length O (D ⧸ Ideal.span {a})).toNat : ℕ) : ℝ) = ∑ᶠ σ : D →ₐ[O] K, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv D _ _ _ _ _ a ha
  classical
  have : Module.Free O D := inferInstance
  obtain ⟨hF, hN⟩ := algebra_norm_eq_prod_embeddings (O := O) (K := K) a
  have hn : Algebra.norm O a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hσ : ∀ σ : D →ₐ[O] K, σ a ≠ 0 := fun σ h => ha (algHom_finite_domain_injective σ (h.trans (map_zero _).symm))
  have h1 : v 1 = 0 := by
    have := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    linarith
  have hp : ∀ s : Finset (D →ₐ[O] K), v (∏ σ ∈ s, σ a) = ∑ σ ∈ s, v (σ a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ,
        hv.mul _ _ (hσ τ) (Finset.prod_ne_zero_iff.2 fun σ _ => hσ σ), ih]
  rw [length_quotient_eq_norm_valuation]
  refine ⟨inferInstance, fun h => hn (IsDiscreteValuationRing.addVal_eq_top_iff.1 h), ?_⟩
  rw [← hv.base _ hn, hN, hp, finsum_eq_sum_of_fintype]
