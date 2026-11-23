import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFarSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_points_lift_mul_inv : ∀ (T S : Scheme.{0}) (f : S ⟶ T) (G : Over T) [GrpObj G] (G' : Over S) [GrpObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G f β → ∀ (Z' : Over S) (Z : Over T) (ζ : Z'.left ⟶ Z.left), ζ ≫ Z.hom = Z'.hom ≫ f → (∀ u : Z ⟶ G, ∃ u' : Z' ⟶ G', u'.left ≫ β = ζ ≫ u.left) ∧ ∀ (u v : Z ⟶ G) (u' v' : Z' ⟶ G'), u'.left ≫ β = ζ ≫ u.left → v'.left ≫ β = ζ ≫ v.left → (u' * v').left ≫ β = ζ ≫ (u * v).left ∧ (u'⁻¹).left ≫ β = ζ ≫ (u⁻¹).left := by
  intro T S f G _ G' _ β hpb Z' Z ζ hζ
  have hw : ∀ u : Z ⟶ G, (ζ ≫ u.left) ≫ G.hom = Z'.hom ≫ f := fun u => by
    rw [Category.assoc, Over.w u, hζ]
  refine ⟨fun u => ⟨Over.homMk (hpb.1.lift (ζ ≫ u.left) Z'.hom (hw u)) (hpb.1.lift_snd _ _ _),
    hpb.1.lift_fst _ _ _⟩, ?_⟩
  intro u v u' v' hu hv
  let ζ' : Over.mk (Z'.hom ≫ f) ⟶ Z := Over.homMk ζ hζ
  let φ : (Z' ⟶ G') → (Over.mk (Z'.hom ≫ f) ⟶ G) := fun w =>
    Over.homMk (w.left ≫ β) (by
      change (w.left ≫ β) ≫ G.hom = Z'.hom ≫ f
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w w])
  have hφ : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    Over.OverMorphism.ext (hpb.2 Z' a b (φ a) (φ b) rfl rfl).symm
  let ψ := MonoidHom.mk' φ hφ
  have hu' : ψ u' = ζ' ≫ u := Over.OverMorphism.ext hu
  have hv' : ψ v' = ζ' ≫ v := Over.OverMorphism.ext hv
  constructor
  · have h : ψ (u' * v') = ζ' ≫ (u * v) := by rw [map_mul, hu', hv', MonObj.comp_mul]
    exact congrArg CommaMorphism.left h
  · have h : ψ (u'⁻¹) = ζ' ≫ (u⁻¹) := by rw [map_inv, hu', GrpObj.comp_inv]
    exact congrArg CommaMorphism.left h

end GlobalTheory.Mum
