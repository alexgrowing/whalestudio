import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericFlatScheme

theorem affine (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : CommRingCat.{0})
    (s : Spec A ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd s (spMap φ)) := by
  obtain ⟨g, rfl⟩ : ∃ g : CommRingCat.of R ⟶ A, Spec.map g = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  have hg : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let : Algebra R A := g.hom.toAlgebra
  have : Algebra.FiniteType R A := hg
  obtain ⟨a, ha, hfree⟩ := (GlobalTheory.generic_freeness R).2.1 A A
  refine ⟨a, ha, fun R' _ φ hφ => ?_⟩
  let : Algebra R R' := φ.toAlgebra

  let : Algebra (Localization.Away a) R' := (IsLocalization.Away.lift a hφ).toAlgebra
  have : IsScalarTower R (Localization.Away a) R' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hφ x).symm
  have := hfree
  have hbc : IsBaseChange (Localization.Away a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) A) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (Localization.Away a) _).mp
      inferInstance
  have : Module.Free (Localization.Away a) (Localization.Away a ⊗[R] A) :=
    Module.Free.of_equiv hbc.equiv.symm
  have hflat : Module.Flat R' (R' ⊗[R] A) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away a) R' R' A).symm

  have hA : g = CommRingCat.ofHom (algebraMap R A) := rfl
  have hF : Flat (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  rw [hA]
  change Flat (pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  rw [← pullbackSymmetry_hom_comp_fst, ← pullbackSpecIso_hom_fst' R R' A]
  infer_instance

end GenericFlatScheme

theorem generic_flatness_scheme :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R),
      LocallyOfFiniteType s → QuasiCompact s → ∃ f : R, f ≠ 0 ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
          Flat (pullback.snd s (spMap φ)) := by
  intro R _ _ _ Z s hs hq
  have := hs
  have := hq
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  let 𝒰 := Z.affineCover.finiteSubcover
  have key : ∀ i, ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd (𝒰.f i ≫ s) (spMap φ)) :=
    fun i => by
      have : LocallyOfFiniteType (𝒰.f i ≫ s) := MorphismProperty.comp_mem _ _ _
        (inferInstance : LocallyOfFiniteType (𝒰.f i)) hs
      exact @GenericFlatScheme.affine R _ _ _ _ (𝒰.f i ≫ s) this
  choose e he0 heF using key
  refine ⟨∏ i, e i, Finset.prod_ne_zero_iff.mpr fun i _ => he0 i, fun R' _ φ hφ => ?_⟩

  have hloc : IsZariskiLocalAtSource @AlgebraicGeometry.Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat)
    (𝒰.pullback₁ (pullback.fst s (spMap φ)))).mpr fun i => ?_
  change Flat (pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ))
  have := heF i R' φ
    (isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem e (Finset.mem_univ _))) hφ)
  have h : pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ) =
      ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso s (spMap φ) (𝒰.f i)).hom) ≫
        pullback.snd (𝒰.f i ≫ s) (spMap φ) := by
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc]
  rw [h]
  infer_instance

end GlobalTheory
