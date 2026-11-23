import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapCompCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelFunctionFieldTrdegEqRelDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegCompositumLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackResidueFieldsGenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionResidueFieldSurjectiveStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Vert.Model

theorem trdeg_fnFld_eq_relDim : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z Z₁ : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom Z₁ Z), letI := f.fnMap.toAlgebra; Algebra.trdeg Z.fnFld Z₁.fnFld = f.relDim := by
  intro O _ _ _ Z Z₁ f
  letI := f.fnMap.toAlgebra
  letI : Algebra O Z.fnFld := Z.fnConst.toAlgebra
  letI : Algebra O Z₁.fnFld := Z₁.fnConst.toAlgebra
  haveI : IsScalarTower O Z.fnFld Z₁.fnFld :=
    IsScalarTower.of_algebraMap_eq fun a => (congrArg (· a) (Hom.fnMap_comp_fnConst f)).symm
  haveI : FaithfulSMul O Z.fnFld :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Z.fnConst_injective
  haveI : FaithfulSMul Z.fnFld Z₁.fnFld :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap Z.fnFld Z₁.fnFld).injective
  have h := trdeg_add_eq O Z.fnFld (A := Z₁.fnFld)
  rw [GlobalTheory.T.model_function_field_trdeg_eq_relDim O Z, GlobalTheory.T.model_function_field_trdeg_eq_relDim O Z₁] at h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Algebra.trdeg Z.fnFld Z₁.fnFld = n :=
    Cardinal.lt_aleph0.1 (lt_of_le_of_lt (self_le_add_left _ _) (h ▸ Cardinal.nat_lt_aleph0 _))
  rw [hn] at h ⊢
  have h' : Z.relDim + n = Z₁.relDim := by exact_mod_cast h
  have h'' := f.relDim_add
  congr 1
  omega

theorem residueFieldMap_comp_apply_eq {X Y W : Scheme.{0}} (a : W ⟶ Y) (b : Y ⟶ X) (c : W ⟶ X)
    (e : a ≫ b = c) (z : W) (p : X) (m : c z = p) (hp : b (a z) = p)
    (x : X.residueField (b (a z))) :
    (a.residueFieldMap z) ((b.residueFieldMap (a z)) x) =
      ((X.residueFieldCongr m).inv ≫ c.residueFieldMap z) ((X.residueFieldCongr hp).hom x) := by
  subst e m
  simp only [Scheme.residueFieldCongr_inv, Scheme.residueFieldMap_comp, CommRingCat.comp_apply]
  rfl

theorem fnFld_closure_eq_top : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B B₁ B₂ Z : GlobalTheory.Vert.Model O) (f₁ : GlobalTheory.Vert.Model.Hom B₁ B) (f₂ : GlobalTheory.Vert.Model.Hom B₂ B)
    (h₁ : GlobalTheory.Vert.Model.Hom Z B₁) (h₂ : GlobalTheory.Vert.Model.Hom Z B₂) (w : h₁.f ≫ f₁.f = h₂.f ≫ f₂.f),
    IsClosedImmersion (pullback.lift h₁.f h₂.f w) →
      Subfield.closure (Set.range h₁.fnMap ∪ Set.range h₂.fnMap) = ⊤ := by
  intro O _ _ _ B B₁ B₂ Z f₁ f₂ h₁ h₂ w hi
  set ι := pullback.lift h₁.f h₂.f w
  set η := genericPoint Z.X
  have hsurj := GlobalTheory.T.closedImmersion_residueField_surjective _ _ ι η
  have hgen := GlobalTheory.T.pullback_residue_fields_generate _ _ _ f₁.f f₂.f (ι η)
  have hle : Subfield.closure
      (Set.range ((pullback.fst f₁.f f₂.f).residueFieldMap (ι η)).hom ∪
        Set.range ((pullback.snd f₁.f f₂.f).residueFieldMap (ι η)).hom) ≤
      (Subfield.closure (Set.range h₁.fnMap ∪ Set.range h₂.fnMap)).comap
        (ι.residueFieldMap η).hom := by
    have hp₁ : (pullback.fst f₁.f f₂.f) (ι η) = genericPoint B₁.X := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
      exact h₁.map_genericPoint
    have hp₂ : (pullback.snd f₁.f f₂.f) (ι η) = genericPoint B₂.X := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
      exact h₂.map_genericPoint
    refine Subfield.closure_le.2 ?_
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · refine Subfield.subset_closure (Or.inl ⟨(B₁.X.residueFieldCongr hp₁).hom x, ?_⟩)
      exact (residueFieldMap_comp_apply_eq ι _ h₁.f (pullback.lift_fst _ _ _) η _
        h₁.map_genericPoint hp₁ x).symm
    · refine Subfield.subset_closure (Or.inr ⟨(B₂.X.residueFieldCongr hp₂).hom x, ?_⟩)
      exact (residueFieldMap_comp_apply_eq ι _ h₂.f (pullback.lift_snd _ _ _) η _
        h₂.map_genericPoint hp₂ x).symm
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨u, rfl⟩ := hsurj z
  exact hle (hgen ▸ Subfield.mem_top u)

theorem relDim_add_le_of_isClosedImmersion : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B B₁ B₂ Z : GlobalTheory.Vert.Model O) (f₁ : GlobalTheory.Vert.Model.Hom B₁ B) (f₂ : GlobalTheory.Vert.Model.Hom B₂ B) (h₁ : GlobalTheory.Vert.Model.Hom Z B₁) (h₂ : GlobalTheory.Vert.Model.Hom Z B₂) (w : h₁.f ≫ f₁.f = h₂.f ≫ f₂.f), IsClosedImmersion (pullback.lift h₁.f h₂.f w) → Z.relDim + B.relDim ≤ B₁.relDim + B₂.relDim := by
  intro O _ _ _ B B₁ B₂ Z f₁ f₂ h₁ h₂ w hi
  letI := f₁.fnMap.toAlgebra
  letI := f₂.fnMap.toAlgebra
  letI := h₁.fnMap.toAlgebra
  have key := GlobalTheory.T.trdeg_compositum_le B.fnFld B₁.fnFld B₂.fnFld Z.fnFld h₂.fnMap
    (Hom.fnMap_comp_eq f₁ f₂ h₁ h₂ w).symm (fnFld_closure_eq_top O B B₁ B₂ Z f₁ f₂ h₁ h₂ w hi)
  rw [trdeg_fnFld_eq_relDim O B₁ Z h₁, trdeg_fnFld_eq_relDim O B B₂ f₂] at key
  have hle : h₁.relDim ≤ f₂.relDim := by exact_mod_cast key
  have a1 := h₁.relDim_add
  have a2 := f₂.relDim_add
  have a3 := f₁.relDim_le
  omega

end GlobalTheory.Vert.Model
