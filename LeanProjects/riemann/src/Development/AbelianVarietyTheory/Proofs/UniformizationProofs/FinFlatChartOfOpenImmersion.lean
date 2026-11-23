import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.Unif

theorem finFlatChart_of_openImmersion {X Y Z S B : Scheme.{0}} (f : X ⟶ B) (s : S ⟶ B)
    (j : Y ⟶ X) [IsOpenImmersion j] (i : Z ⟶ S) [IsOpenImmersion i] (p : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [Nonempty Z] (h : p ≫ i ≫ s = j ≫ f) :
    ∃ (W : X.Opens) (V : S.Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧
      IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ s = W.ι ≫ f := by
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary Z)
  refine ⟨j.opensRange, i.opensRange, j.isoOpensRange.inv ≫ p ≫ i.isoOpensRange.hom,
    ⟨j y, y, rfl⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, h]
  rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι_assoc]

theorem exists_finFlat_away (R A : Type) [CommRing R] [CommRing A] [IsDomain R]
    [IsNoetherianRing R] (φ : R →+* A) (hφ : φ.Finite) (hi : Function.Injective φ) :
    ∃ (Y Z : Scheme.{0}) (j : Y ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ Spec (CommRingCat.of R))
      (p : Y ⟶ Z), IsOpenImmersion j ∧ IsOpenImmersion i ∧ IsFinite p ∧ Flat p ∧ Surjective p ∧
      Nonempty Z ∧ p ≫ i = j ≫ Spec.map (CommRingCat.ofHom φ) := by
  algebraize [φ]
  have : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) A) (FractionRing R)
  have hfree' : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) A)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) A)
  have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [IsFinite.SpecMap_iff]; exact hφ
  have h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨hφ.to_isIntegral.comap_surjective hi⟩
  have h3 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    inferInstance
  have hd : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (Submonoid.powers_le.mpr hr)
  refine ⟨_, _, _, _, _, MorphismProperty.of_isPullback hpb h3, h3,
    MorphismProperty.of_isPullback hpb.flip h1, ?_, MorphismProperty.of_isPullback hpb.flip h2,
    inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away r))), hpb.w⟩
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff (R := Localization.Away r)
    (S := Localization.Away r ⊗[R] A)).mpr inferInstance

theorem exists_finite_flat_chart : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f], ∃ (g : ℕ) (W : X.Opens) (V : (Spec (CommRingCat.of (MvPolynomial (Fin g) K))).Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧ IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) = W.ι ≫ f := by
  intro K _ X _ f _
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  have hft : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  have hft' : ψ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  letI : Algebra K Γ(X, U) := ψ.hom.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hft'
  obtain ⟨g, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K Γ(X, U)
  obtain ⟨Y, Z, j, i, p, _, _, _, _, _, _, h⟩ :=
    exists_finFlat_away _ _ φ.toRingHom hfin hinj
  refine ⟨g, finFlatChart_of_openImmersion f _ (j ≫ hU.fromSpec) i p ?_⟩
  rw [reassoc_of% h, Category.assoc, ← hψ, ← Spec.map_comp]
  congr 2
  ext x
  exact φ.commutes x

end GlobalTheory.Unif
