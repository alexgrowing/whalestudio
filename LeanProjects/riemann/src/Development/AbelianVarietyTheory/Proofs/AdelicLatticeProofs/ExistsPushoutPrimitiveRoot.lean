import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isField_tensor_of_coprime (F A B : Type) [Field F] [Field A] [Field B] [Algebra F A]
    [Algebra F B] (h : Nat.Coprime (Module.finrank F A) (Module.finrank F B)) :
    IsField (A ⊗[F] B) := by
  refine IntermediateField.LinearDisjoint.isField_of_forall F A B ?_
  intro K _ _ fa fb
  apply IntermediateField.LinearDisjoint.of_finrank_coprime
  have ha : Module.finrank F A = Module.finrank F fa.fieldRange :=
    (AlgEquiv.ofInjectiveField fa).toLinearEquiv.finrank_eq
  have hb : Module.finrank F B = Module.finrank F fb.fieldRange :=
    (AlgEquiv.ofInjectiveField fb).toLinearEquiv.finrank_eq
  rwa [← ha, ← hb]

theorem coprime_finrank_cyclotomic (p : ℕ) (hp : p.Prime) (F A : Type) [Field F] [Field A]
    [Algebra F A] [IsCyclotomicExtension {p} F A] : Nat.Coprime (Module.finrank F A) p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Module.Finite F A := IsCyclotomicExtension.finite {p} F A
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hdvd : minpoly F (IsCyclotomicExtension.zeta p F A) ∣ cyclotomic p F := by
    apply minpoly.dvd
    rw [aeval_def, ← eval_map, map_cyclotomic]
    haveI : NeZero (p : A) := hζ.neZero'
    exact (isRoot_cyclotomic_iff.mpr hζ)
  have hle := natDegree_le_of_dvd hdvd (cyclotomic_ne_zero p F)
  rw [natDegree_cyclotomic, Nat.totient_prime hp] at hle
  have hfr : Module.finrank F A = (minpoly F (IsCyclotomicExtension.zeta p F A)).natDegree := by
    rw [(hζ.powerBasis F).finrank, ← (hζ.powerBasis F).natDegree_minpoly,
      IsPrimitiveRoot.powerBasis_gen]
  have hpos : 0 < Module.finrank F A := Module.finrank_pos
  have h1 := hp.pos
  exact (Nat.coprime_of_lt_prime hpos.ne' (by omega) hp).symm

theorem exists_pushout_primitiveRoot : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], p.Prime → p ≠ 2 → Module.finrank F E = p → ∃ (F' E' : Type) (_ : Field F') (_ : NumberField F') (_ : Field E') (_ : NumberField E') (_ : Algebra F F') (_ : Algebra F' E') (_ : Algebra E E') (_ : Algebra F E') (_ : IsScalarTower F F' E') (_ : IsScalarTower F E E') (ζ : F'), Algebra.IsPushout F F' E E' ∧ IsTotallyComplex F' ∧ IsGalois F' E' ∧ IsPrimitiveRoot ζ p ∧ Module.finrank F' E' = p ∧ Nat.Coprime (Module.finrank F F') p := by
  intro p F E _ _ _ _ _ _ hp h2 hdeg
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : Type := CyclotomicField p F
  haveI : IsCyclotomicExtension {p} F A := CyclotomicField.isCyclotomicExtension p F
  haveI : NumberField A := IsCyclotomicExtension.numberField {p} F A
  have hco := coprime_finrank_cyclotomic p hp F A
  have hf : IsField (A ⊗[F] E) := isField_tensor_of_coprime F A E (by rwa [hdeg])
  letI : Field (A ⊗[F] E) := hf.toField
  letI : Algebra E (A ⊗[F] E) := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Module.Finite A (A ⊗[F] E) := inferInstance
  haveI : NumberField (A ⊗[F] E) := NumberField.of_module_finite A (A ⊗[F] E)
  have hζ := IsCyclotomicExtension.zeta_spec p F A
  have hr : Module.finrank A (A ⊗[F] E) = p := by
    rw [Module.finrank_baseChange, hdeg]
  have h3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
  refine ⟨A, A ⊗[F] E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    IsCyclotomicExtension.zeta p F A, inferInstance, ?_, ?_, hζ, hr, hco⟩
  · exact NumberField.nrRealPlaces_eq_zero_iff.mp
      (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt h3 hζ)
  · apply IsGalois.of_card_aut_eq_finrank
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
    · rw [Module.finrank_baseChange, ← IsGalois.card_aut_eq_finrank]
      refine Nat.card_le_card_of_injective
        (fun g : E ≃ₐ[F] E => (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) g)) ?_
      intro g h hgh
      ext x
      have := DFunLike.congr_fun hgh ((1 : A) ⊗ₜ[F] x)
      simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul] at this
      exact (algebraMap E (A ⊗[F] E)).injective this

end GlobalTheory.CNorm
