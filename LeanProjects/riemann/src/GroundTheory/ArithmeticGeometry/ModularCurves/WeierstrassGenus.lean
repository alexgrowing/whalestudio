import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCechCurve
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.PSpaceFinite
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistLeray

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

namespace GroundTheory.Arith.Modular

section Restrict

lemma presheaf_map_map_apply {Y : Scheme.{u}} {A B C : Y.Opens} (f : op C ⟶ op B) (g : op B ⟶ op A)
    (s : Γ(Y, C)) : Y.presheaf.map g (Y.presheaf.map f s) = Y.presheaf.map (f ≫ g) s := by
  rw [Functor.map_comp, CommRingCat.comp_apply]

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma awayToSection_one_fromZero (z : 𝒜 0) :
    Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun s => (Proj.basicOpen 𝒜 1).topIso.hom s) (ι_appTop_toSpecZero 𝒜 z)
  simp only [CategoryTheory.Iso.inv_hom_id_apply] at h
  rw [← h, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact presheaf_map_map_apply _ _ _

lemma awayToSection_fromZero {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (z : 𝒜 0) :
    Proj.awayToSection 𝒜 f (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z))
    (Proj.awayMap_awayToSection 𝒜 hf (one_mul f).symm)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom] at h
  rw [h, awayToSection_one_fromZero, presheaf_map_map_apply]
  rfl

end Restrict

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Scalars

end Scalars

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section CoverFacts

noncomputable instance curveOver : (Curve W).Over (Spec (.of R)) := ⟨toSpec W⟩

end CoverFacts

section Genus

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

end Genus

end Weierstrass

end GroundTheory.Arith.Modular
