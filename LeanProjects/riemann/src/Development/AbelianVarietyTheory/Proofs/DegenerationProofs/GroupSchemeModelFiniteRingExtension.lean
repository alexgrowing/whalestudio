import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SS

theorem baseChange_iso_tower (K K' V' V'' L : Type) [CommRing K] [CommRing K'] [CommRing V'] [CommRing V''] [CommRing L]
    [Algebra K K'] [Algebra V' K'] [Algebra V' V''] [Algebra V'' L] [Algebra K L] (j : K' →+* L)
    (t : j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V''))
    (e₂ : algebraMap K L = j.comp (algebraMap K K'))
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (G : Over (Spec (CommRingCat.of V'))) [GrpObj G]
    (e : baseChange V' K' G ≅ baseChange K K' A) (he : IsMonHom e.hom) :
    ∃ e : baseChange V'' L (baseChange V' V'' G) ≅ baseChange K L A, IsMonHom e.hom := by
  have s₁ : specMap V'' L ≫ specMap V' V'' = spMap j ≫ specMap V' K' := by
    show spMap (algebraMap V'' L) ≫ spMap (algebraMap V' V'') = spMap j ≫ spMap (algebraMap V' K')
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, t]
  have s₂ : spMap j ≫ 𝟙 _ ≫ specMap K K' = specMap K L := by
    show spMap j ≫ 𝟙 _ ≫ spMap (algebraMap K K') = spMap (algebraMap K L)
    rw [Category.id_comp, e₂, ← Spec.map_comp]; rfl
  have p₁ := ((isGrpPullback_pullback (baseChange V' V'' G) (specMap V'' L)).comp
    (isGrpPullback_pullback G (specMap V' V''))).congr s₁ rfl
  have p₂ := (isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    (isGrpPullback_pullback G (specMap V' K'))
  have p₃ := ((isGrpPullback_pullback (baseChange V' K' G) (spMap j)).comp
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A (specMap K K')))).congr s₂ rfl
  obtain ⟨i₁, hi₁, -⟩ := grpPullback_iso p₁ p₂
  obtain ⟨i₂, hi₂, -⟩ := grpPullback_iso p₃ (isGrpPullback_pullback A (specMap K L))
  refine ⟨i₁ ≪≫ i₂, ?_⟩
  rw [Iso.trans_hom]; infer_instance

theorem exists_finite_frac (V' K' V'' L : Type) [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    [CommRing V''] [IsDomain V''] [Algebra V' V''] [Field L] [Algebra V'' L] [IsFractionRing V'' L]
    (hf : Module.Finite V' V'') (hi : Function.Injective (algebraMap V' V'')) :
    ∃ j : K' →+* L, j.Finite ∧ j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') := by
  have : FaithfulSMul V' V'' := (faithfulSMul_iff_algebraMap_injective V' V'').2 hi
  have hinj : Function.Injective ((algebraMap V'' L).comp (algebraMap V' V'')) :=
    (IsFractionRing.injective V'' L).comp hi
  obtain ⟨j, t⟩ : ∃ j : K' →+* L, j.comp (algebraMap V' K') = (algebraMap V'' L).comp (algebraMap V' V'') :=
    ⟨IsFractionRing.lift (K := K') hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩
  let a₁ : Algebra V' L := ((algebraMap V'' L).comp (algebraMap V' V'')).toAlgebra
  let a₂ : Algebra K' L := j.toAlgebra
  have : IsScalarTower V' V'' L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V' K' L := IsScalarTower.of_algebraMap_eq' t.symm
  have : IsLocalization (Algebra.algebraMapSubmonoid V'' (nonZeroDivisors V')) L := inferInstance
  have h : Module.Finite K' L := Module.Finite.of_isLocalization V' V'' (nonZeroDivisors V')
  exact ⟨j, h, t⟩

theorem model_finite_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (V' : Type) [CommRing V'] [IsDomain V'] [Algebra V V'] [Algebra V' K'] [IsFractionRing V' K'], (algebraMap V' K').comp (algebraMap V V') = (algebraMap K K').comp (algebraMap V K) → ∀ (G : Over (Spec (CommRingCat.of V'))) [GrpObj G], (∃ e : baseChange V' K' G ≅ baseChange K K' A, IsMonHom e.hom) → ∀ (V'' : Type) [CommRing V''] [IsDomain V''] [Algebra V' V''], Module.Finite V' V'' → Function.Injective (algebraMap V' V'') → ∃ (_ : Algebra K (FractionRing V'')) (_ : FiniteDimensional K (FractionRing V'')), (algebraMap V'' (FractionRing V'')).comp ((algebraMap V' V'').comp (algebraMap V V')) = (algebraMap K (FractionRing V'')).comp (algebraMap V K) ∧ ∃ e : baseChange V'' (FractionRing V'') (baseChange V' V'' G) ≅ baseChange K (FractionRing V'') A, IsMonHom e.hom := by
  intro V _ _ _ K _ _ _ A _ K' _ _ hK V' _ _ _ _ _ hc G _ ⟨e, he⟩ V'' _ _ _ hf hi
  obtain ⟨j, hj, t⟩ := exists_finite_frac V' K' V'' (FractionRing V'') hf hi
  let aK : Algebra K (FractionRing V'') := (j.comp (algebraMap K K')).toAlgebra
  have e₂ : algebraMap K (FractionRing V'') = j.comp (algebraMap K K') := rfl
  refine ⟨aK, hj.comp (RingHom.finite_algebraMap.2 hK), ?_, baseChange_iso_tower K K' V' V'' _ j t e₂ A G e he⟩
  rw [e₂, ← RingHom.comp_assoc, ← t, RingHom.comp_assoc, hc, RingHom.comp_assoc]

end GlobalTheory.SS
