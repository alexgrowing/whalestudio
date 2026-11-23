import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.StmtFields

open NumberField Formalism.HC UpperTheory.Top UpperTheory.V

theorem UpperTheory.V.exists_numberField_isAbField_finrank_eq_deg :
    ∀ A : AbF, ∃ (L : Type) (_ : Field L) (_ : NumberField L), IsAbField A L ∧ Module.finrank ℚ L = A.deg := by
  intro A
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  haveI : NeZero ((A.m : ℚ)) := ⟨by exact_mod_cast A.pos.ne'⟩
  haveI hcyc : IsCyclotomicExtension {A.m} ℚ (CyclotomicField A.m ℚ) :=
    CyclotomicField.isCyclotomicExtension A.m ℚ
  haveI : IsGalois ℚ (CyclotomicField A.m ℚ) :=
    IsCyclotomicExtension.isGalois {A.m} ℚ (CyclotomicField A.m ℚ)
  have hirr := Polynomial.cyclotomic.irreducible_rat A.pos
  let e := IsCyclotomicExtension.autEquivPow (CyclotomicField A.m ℚ) hirr
  let G : Subgroup Gal(CyclotomicField A.m ℚ/ℚ) := A.H.comap e.toMonoidHom
  let F := IntermediateField.fixedField G
  refine ⟨F, inferInstance, inferInstance, ?_, ?_⟩
  · have hζ := IsCyclotomicExtension.zeta_spec A.m ℚ (CyclotomicField A.m ℚ)
    refine ⟨A.m, inferInstance, F.val, IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ),
      dvd_rfl, hζ, ?_⟩
    intro τ a hτ
    have hspec := IsPrimitiveRoot.autToPow_spec ℚ hζ τ
    have he : ((e τ : (ZMod A.m)ˣ) : ZMod A.m) = a := by
      have h1 : IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ) ^ ((e τ : (ZMod A.m)ˣ) : ZMod A.m).val
          = IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ) ^ a := by
        rw [← hτ, ← hspec]
        rfl
      have hfin : IsOfFinOrder (IsCyclotomicExtension.zeta A.m ℚ (CyclotomicField A.m ℚ)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨A.m, A.pos, hζ.pow_eq_one⟩
      rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
      rw [← ZMod.natCast_zmod_val ((e τ : (ZMod A.m)ˣ) : ZMod A.m)]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h1
    have hfix : (∀ x : F, τ (F.val x) = F.val x) ↔ τ ∈ G := by
      rw [← IntermediateField.fixingSubgroup_fixedField G, IntermediateField.mem_fixingSubgroup_iff]
      constructor
      · intro h x hx
        exact h ⟨x, hx⟩
      · intro h x
        exact h x.1 x.2
    have hker : τ ∈ G ↔ A.ker a := by
      rw [Subgroup.mem_comap]
      constructor
      · intro h
        exact ⟨e τ, h, he⟩
      · rintro ⟨u, hu, hua⟩
        have hue : u = e τ := Units.ext (hua.trans he.symm)
        have hmem : e τ ∈ A.H := hue ▸ hu
        exact hmem
    exact hfix.trans hker
  · have h1 := Module.finrank_mul_finrank ℚ F (CyclotomicField A.m ℚ)
    rw [IntermediateField.finrank_fixedField_eq_card,
      ← IsGalois.card_aut_eq_finrank ℚ (CyclotomicField A.m ℚ),
      ← Subgroup.index_mul_card G] at h1
    have hpos : 0 < Nat.card G := Nat.card_pos
    have h2 : Module.finrank ℚ F = G.index := Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h2]
    exact Subgroup.index_comap_of_surjective _ e.surjective
