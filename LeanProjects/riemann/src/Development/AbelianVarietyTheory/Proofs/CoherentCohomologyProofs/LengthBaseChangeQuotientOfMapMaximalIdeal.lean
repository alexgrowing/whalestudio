import Mathlib

open IsLocalRing TensorProduct

namespace GlobalTheory

section Local

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

theorem nonempty_baseChange_subquotient_equiv [Module.Flat R S] {X : Type*} [AddCommGroup X]
    [Module R X] (A B : Submodule R X) :
    Nonempty ((S ⊗[R] (A ⧸ B.submoduleOf A)) ≃ₗ[S]
      (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S))) := by
  let h : S ⊗[R] A →ₗ[S] S ⊗[R] (A ⧸ B.submoduleOf A) := (B.submoduleOf A).mkQ.baseChange S
  let g : S ⊗[R] A →ₗ[S] (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) :=
    ((B.baseChange S).submoduleOf (A.baseChange S)).mkQ ∘ₗ A.toBaseChange S
  have hh : Function.Surjective h :=
    LinearMap.lTensor_surjective S (B.submoduleOf A).mkQ_surjective
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (A.toBaseChange_surjective S)
  have e₁ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.submoduleOf A).mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have e₂ : Function.Exact ((B.submoduleOf A).subtype.lTensor S)
      ((B.mkQ ∘ₗ A.subtype).lTensor S) := by
    apply Module.Flat.lTensor_exact S
    rw [LinearMap.exact_iff, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.range_subtype]
    rfl
  have e₃ : Function.Exact (B.subtype.lTensor S) (B.mkQ.lTensor S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ _)
  have hker : LinearMap.ker h = LinearMap.ker g := by
    ext x
    have h1 : x ∈ LinearMap.ker h ↔ (B.submoduleOf A).mkQ.lTensor S x = 0 := Iff.rfl
    have h2 : x ∈ LinearMap.ker g ↔ A.subtype.lTensor S x ∈ B.baseChange S := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      rfl
    rw [h1, h2, e₁ x, ← e₂ x, LinearMap.lTensor_comp, LinearMap.comp_apply, e₃]
    rfl
  exact ⟨(h.quotKerEquivOfSurjective hh).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    g.quotKerEquivOfSurjective hg⟩

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
  (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_flat :
    Module.length S (S ⊗[R] X) =
      Module.length R X * Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
  IsLocalRing.length_baseChange R S X

variable {X} in

theorem length_baseChange_subquotient_flat (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) *
        Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  rw [← length_baseChange_flat]
  exact (nonempty_baseChange_subquotient_equiv R S A B).some.length_eq.symm

variable {R S}

end Local

section DVR

open IsDiscreteValuationRing hiding maximalIdeal

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

theorem length_quotient_span_singleton_eq_addVal {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] (x : S) :
    Module.length S (S ⧸ Ideal.span {x}) = addVal S x := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  rcases eq_or_ne x 0 with rfl | hx
  · rw [addVal_zero, Ideal.span_singleton_zero,
      (Submodule.quotEquivOfEqBot (⊥ : Ideal S) rfl).length_eq]
    by_contra h
    have h' := Module.length_ne_top_iff.mp h
    rw [← isArtinianRing_iff_isFiniteLength] at h'
    exact not_isField S (IsArtinianRing.isField_of_isDomain S)
  · obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hπ
    rw [addVal_def' u hπ, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq, length_quotient_pow_maximalIdeal]

variable [IsLocalHom (algebraMap R S)]

theorem map_maximalIdeal_eq_pow_ramificationIdx :
    (maximalIdeal R).map (algebraMap R S) =
      maximalIdeal S ^ ((maximalIdeal S).ramificationIdx R) := by
  have hp : maximalIdeal R ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hpS : (maximalIdeal R).map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hpS hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hn
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal R) (maximalIdeal S) hp,
    Ideal.ramificationIdx'_spec (n := n) hn.le, hn]
  rw [hn]
  exact (Ideal.pow_succ_lt_pow (IsDiscreteValuationRing.not_a_field S) n).not_ge

theorem length_fibre_eq_ramificationIdx :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) =
      ((maximalIdeal S).ramificationIdx R : ℕ) := by
  conv_lhs => rw [map_maximalIdeal_eq_pow_ramificationIdx]
  exact length_quotient_pow_maximalIdeal S _

theorem ramificationIdx_maximalIdeal_pos : 0 < (maximalIdeal S).ramificationIdx R := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have := map_maximalIdeal_eq_pow_ramificationIdx R S
  rw [h, pow_zero, Ideal.one_eq_top] at this
  exact (map_maximalIdeal_lt_top (algebraMap R S)).ne this

variable {R} in

theorem addVal_algebraMap_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) :
    addVal S (algebraMap R S ϖ) = ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [← length_fibre_eq_ramificationIdx, ← length_quotient_span_singleton_eq_addVal,
    hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

variable {R} in

theorem addVal_algebraMap (x : R) :
    addVal S (algebraMap R S x) = addVal R x * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.top_mul]
    exact_mod_cast (ramificationIdx_maximalIdeal_pos R S).ne'
  · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
    rw [addVal_def' u hϖ, map_mul, map_pow, addVal_mul, addVal_pow,
      addVal_algebraMap_uniformizer S hϖ,
      addVal_eq_zero_iff.mpr (u.isUnit.map (algebraMap R S)), zero_add, nsmul_eq_mul]

variable (X : Type*) [AddCommGroup X] [Module R X]

theorem length_baseChange_dvr :
    Module.length S (S ⊗[R] X) =
      Module.length R X * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_flat, length_fibre_eq_ramificationIdx]

variable {X} in

theorem length_baseChange_subquotient_dvr (A B : Submodule R X) :
    Module.length S (A.baseChange S ⧸ (B.baseChange S).submoduleOf (A.baseChange S)) =
      Module.length R (A ⧸ B.submoduleOf A) * ((maximalIdeal S).ramificationIdx R : ℕ) := by
  rw [length_baseChange_subquotient_flat, length_fibre_eq_ramificationIdx]

end DVR

section Uniformizer

open IsDiscreteValuationRing hiding maximalIdeal

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [Algebra R S] [FaithfulSMul R S]

end Uniformizer

end GlobalTheory
