import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

open scoped TensorProduct

private theorem finite_projective_of_free_int (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N]
    [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N] :
    Module.Finite (𝓞 E) N ∧ Module.Projective (𝓞 E) N := by
  haveI : Module.Finite (𝓞 E) N := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) N
  haveI : Module.IsTorsionFree (𝓞 E) N := by
    refine Module.isTorsionFree_iff_smul_eq_zero.2 fun a x hax => ?_
    by_contra hk
    push_neg at hk
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    have h0 : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hk.1
    have h1 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hc, mul_smul, hax, smul_zero]
    exact hk.2 ((smul_eq_zero.1 h1).resolve_left (by exact_mod_cast h0))
  haveI : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

private theorem finrank_quot_tensor {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    [Module.Finite O N] [Module.Projective O N] (I : Ideal O) [I.IsMaximal] :
    Module.finrank (O ⧸ I) ((O ⧸ I) ⊗[O] N) = Module.finrank O N := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field _
  have h1 := Module.rankAtStalk_baseChange (R := O) (M := N) (S := O ⧸ I) ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
  exact h1

private theorem one_tmul_eq_zero_iff {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O) (x : N) :
    (1 : O ⧸ I) ⊗ₜ[O] x = 0 ↔ x ∈ I • (⊤ : Submodule O N) := by
  rw [← (TensorProduct.quotTensorEquivQuotSMul N I).map_eq_zero_iff,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

private theorem one_tmul_surjective {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] (I : Ideal O)
    (t : (O ⧸ I) ⊗[O] N) : ∃ x : N, (1 : O ⧸ I) ⊗ₜ[O] x = t := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.quotTensorEquivQuotSMul N I t)
  refine ⟨x, (TensorProduct.quotTensorEquivQuotSMul N I).injective ?_⟩
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, hx]

theorem exists_ker_vec_of_not_onto_mod {O P X : Type} [CommRing O] [IsDomain O] [AddCommGroup P] [Module O P]
    [Module.Finite O P] [Module.Projective O P] [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (f : P →ₗ[O] X) (hr : Module.finrank O P = Module.finrank O X) (I : Ideal O)
    (hI : I.IsMaximal) (hi : LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≠ ⊤) :
    ∃ v : P, f v ∈ I • (⊤ : Submodule O X) ∧ ∃ ℓ : P →ₗ[O] O, ℓ v ∉ I := by
  letI : Field (O ⧸ I) := Ideal.Quotient.field _
  have hns : ¬ Function.Surjective (f.baseChange (O ⧸ I)) := fun hs => hi <| eq_top_iff.2 fun x _ => by
    obtain ⟨t, ht⟩ := hs (1 ⊗ₜ x)
    obtain ⟨v, rfl⟩ := one_tmul_surjective I t
    rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub, one_tmul_eq_zero_iff] at ht
    have : x = f v - (f v - x) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left ⟨v, rfl⟩) (Submodule.mem_sup_right ht)
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [finrank_quot_tensor, finrank_quot_tensor, hr]), injective_iff_map_eq_zero] at hns
  push_neg at hns
  obtain ⟨t, ht, ht0⟩ := hns
  obtain ⟨v, rfl⟩ := one_tmul_surjective I t
  rw [LinearMap.baseChange_tmul, one_tmul_eq_zero_iff] at ht
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero (O ⧸ I) ht0
  obtain ⟨ℓ, hℓ⟩ := Module.projective_lifting_property I.mkQ
    ((g.restrictScalars O).comp (TensorProduct.mk O (O ⧸ I) P 1)) I.mkQ_surjective
  refine ⟨v, ht, ℓ, fun hv => hg ?_⟩
  have := LinearMap.congr_fun hℓ v
  exact this.symm.trans ((Submodule.Quotient.mk_eq_zero I).2 hv)

theorem IsOpp.exists_ker_vec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 := by
  intro E _ _ _ H D X _ _ _ _ y Z Z' h hr 𝔭 h𝔭 hi
  obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
  obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
  obtain ⟨_, _⟩ := finite_projective_of_free_int E Z'
  obtain ⟨_, _⟩ := finite_projective_of_free_int E X
  have hrank : Module.finrank (𝓞 E) Z' = Module.finrank (𝓞 E) X := by
    have := h.finrank_int_eq
    rw [GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z'] at this
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos this).trans hr
  refine exists_ker_vec_of_not_onto_mod (y.comp Z'.subtype) hrank 𝔭 h𝔭 ?_
  rwa [LinearMap.range_comp, Submodule.range_subtype]

end GlobalTheory.LowFilt
