import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj ComplexOrder in

theorem _root_.GlobalTheory.LamF.exists_mulEquiv_points_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f φ → ∀ T : Over S', ∃ Φ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (Φ x).left = x.left ≫ φ := by
  intro S S' f G G' _ _ φ hφ T
  obtain ⟨hpb, hmul⟩ := hφ
  let toFun : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w])
  let invFun : (Over.mk (T.hom ≫ f) ⟶ G) → (T ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left T.hom (by simpa using Over.w y)) (hpb.lift_snd _ _ _)
  have hto : ∀ x, (toFun x).left = x.left ≫ φ := fun x => rfl
  refine ⟨{ toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, hto⟩
  · intro x
    ext1
    refine hpb.hom_ext ?_ ?_
    · exact hpb.lift_fst _ _ _
    · exact (hpb.lift_snd _ _ _).trans (Over.w x).symm
  · intro y
    ext1
    exact hpb.lift_fst _ _ _
  · intro x y
    ext1
    exact (hmul T x y (toFun x) (toFun y) (hto x) (hto y)).symm

end GlobalTheory.LamF
