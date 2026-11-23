import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_finset_isPushout_model (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
      ∃ (A₀ : CommRingCat.{0}) (f : CommRingCat.of k ⟶ A₀) (g : A₀ ⟶ CommRingCat.of A),
        IsPushout f (CommRingCat.ofHom β) g (CommRingCat.ofHom (algebraMap K A)) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let P := Algebra.Presentation.ofFinitePresentation K A
  refine ⟨P.finite_coeffs.toFinset, fun k _ β hs => ?_⟩
  letI : Algebra k K := β.toAlgebra
  letI : Algebra k A := ((algebraMap K A).comp β).toAlgebra
  haveI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  haveI : P.HasCoeffs k := ⟨fun x hx => hs (by simpa using hx)⟩
  let e := P.tensorModelOfHasCoeffsEquiv k
  have h := (CommRingCat.isPushout_tensorProduct k K (P.ModelOfHasCoeffs k)).flip
  refine ⟨CommRingCat.of (P.ModelOfHasCoeffs k), CommRingCat.ofHom (algebraMap k _),
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom) ≫
      e.toRingEquiv.toCommRingCatIso.hom, ?_⟩
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso
    ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · ext x
    exact e.commutes x

theorem exists_finset_model_of_isAffine :
    ∀ (K : Type) [Field K] (X : Over (Sp K)), IsAffine X.left → LocallyOfFiniteType X.hom →
      ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
        ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β) := by
  intro K _ X hX hft
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := Γ(X.left, ⊤))
    (X.left.isoSpec.inv ≫ X.hom)
  have h1 : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h1
  letI : Algebra K Γ(X.left, ⊤) := ψ.hom.toAlgebra
  haveI : Algebra.FiniteType K Γ(X.left, ⊤) := h1
  obtain ⟨s, hs⟩ := exists_finset_isPushout_model K Γ(X.left, ⊤)
  refine ⟨s, fun k _ β hβ => ?_⟩
  obtain ⟨A₀, f, g, h⟩ := hs k β hβ
  have h2 : IsPullback (Spec.map g) (Spec.map ψ) (Spec.map f) (spMap β) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ h
  refine ⟨Over.mk (Spec.map f), X.left.isoSpec.hom ≫ Spec.map g, ?_⟩
  refine h2.of_iso X.left.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [hψ]
  · simp
  · simp

end GlobalTheory
