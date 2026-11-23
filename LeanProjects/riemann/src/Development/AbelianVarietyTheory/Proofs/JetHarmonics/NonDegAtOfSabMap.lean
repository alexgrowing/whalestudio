import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CubWeilOneIffPairOne
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaPair

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

def cobCube {A U : Type} [CommGroup A] [CommGroup U] (h : A → U) (x x' y : A) : U :=
  h (x * x' * y) * (h (x * x'))⁻¹ * (h (x * y))⁻¹ * (h (x' * y))⁻¹ * h x * h x' * h y * (h 1)⁻¹

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] in
omit [IsCommMonObj G] [IsCommMonObj G'] in

theorem _root_.GlobalTheory.AlphaPair.exists_ptEquiv {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {Z : Scheme.{0}}
    (a : Z ⟶ S') (b : Z ⟶ S) (hb : b = a ≫ f) :
    ∃ ρ : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  have hpb : IsPullback F G'.hom G.hom f := gp.1
  let φ : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ F) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w x]
      rfl)
  let ψ : (Over.mk (a ≫ f) ⟶ G) → (Over.mk a ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left a (by simpa using Over.w y)) (by simp)
  refine ⟨{ toFun := φ, invFun := ψ, left_inv := ?_, right_inv := ?_, map_mul' := ?_ },
    fun x => rfl⟩
  · intro x
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simp [φ, ψ]
    · simp [φ, ψ]
  · intro y
    apply Over.OverMorphism.ext
    simp [φ, ψ]
  · intro x y
    apply Over.OverMorphism.ext
    exact (gp.2 (Over.mk a) x y (φ x) (φ y) rfl rfl).symm

end GlobalTheory.AlphaPair
