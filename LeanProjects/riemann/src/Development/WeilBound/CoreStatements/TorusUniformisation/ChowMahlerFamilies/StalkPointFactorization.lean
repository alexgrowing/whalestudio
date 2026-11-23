import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.StalkPointFactorization

theorem ext_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {S T : CommRingCat.{0}} (i : S ⟶ T)
    (hi : Function.Injective i.hom) (f g : Spec S ⟶ X) (hf : ∀ z, f z ∈ U) (hg : ∀ z, g z ∈ U)
    (e : Spec.map i ≫ f = Spec.map i ≫ g) : f = g := by
  have hf' : Set.range f ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hf z
  have hg' : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact hg z
  obtain ⟨a, ha⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec f hf')
  obtain ⟨b, hb⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec g hg')
  have ea : Spec.map a ≫ hU.fromSpec = f := by rw [ha, IsOpenImmersion.lift_fac]
  have eb : Spec.map b ≫ hU.fromSpec = g := by rw [hb, IsOpenImmersion.lift_fac]
  rw [← ea, ← eb, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at e
  have e2 : a ≫ i = b ≫ i := Spec.map_injective e
  have e3 : a = b := by
    ext s
    apply hi
    exact ConcreteCategory.congr_hom e2 s
  rw [← ea, ← eb, e3]

theorem fromSpecStalk_mem {X : Scheme.{0}} {U : X.Opens} {y : X} (hy : y ∈ U) (z : Spec (X.presheaf.stalk y)) :
    X.fromSpecStalk y z ∈ U := by
  have h : X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact Specializes.mem_open h U.isOpen hy

end PositivityTheory.Xgn.StalkPointFactorization

theorem PositivityTheory.Xgn.stalk_point_factorization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ (U : X.Opens), IsAffineOpen U → ∀ (R : Type) [CommRing R] (φ : R →+* Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap φ ≫ x = ξ → (∀ z, x z ∈ U) → ∀ (q : Cpt ξ), q.1 ∈ U → ∀ ψ : R →+* X.presheaf.stalk q.1, (genMap ξ q).comp ψ = φ → spMap ψ ≫ x = X.fromSpecStalk q.1 := by
  intro X Ω _ ξ hξ U hU R _ φ x hx hxU q hq ψ hψ
  refine PositivityTheory.Xgn.StalkPointFactorization.ext_of_affine hU (S := X.presheaf.stalk q.1) (T := CommRingCat.of Ω)
    (CommRingCat.ofHom (genMap ξ q)) (hξ.inj q) (spMap ψ ≫ x) (X.fromSpecStalk q.1) (fun z => hxU (spMap ψ z))
    (PositivityTheory.Xgn.StalkPointFactorization.fromSpecStalk_mem hq) ?_
  have h1 : spMap (genMap ξ q) ≫ spMap ψ = spMap φ := by
    rw [← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h2 : spMap (genMap ξ q) ≫ spMap ψ ≫ x = ξ := by
    rw [← Category.assoc, h1, hx]
  exact h2.trans (GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk q).symm
