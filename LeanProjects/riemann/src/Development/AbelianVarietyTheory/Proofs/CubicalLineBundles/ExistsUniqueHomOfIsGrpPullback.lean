import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMulEquivPointsOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem existsUnique_hom_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G G₁ : Over S) (G' G₁' : Over S') [GrpObj G] [GrpObj G'] [GrpObj G₁] [GrpObj G₁'] (φ : G'.left ⟶ G.left) (φ₁ : G₁'.left ⟶ G₁.left), IsGrpPullback G' G f φ → IsGrpPullback G₁' G₁ f φ₁ → ∀ F : G ⟶ G₁, (∃! F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left) ∧ ∀ F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left → IsMonHom F → IsMonHom F' := by
  intro S S' f G G₁ G' G₁' _ _ _ _ φ φ₁ h h₁ F
  refine ⟨⟨Over.homMk (h₁.1.lift (φ ≫ F.left) G'.hom ?_) (h₁.1.lift_snd _ _ _),
    h₁.1.lift_fst _ _ _, fun F' hF' => ?_⟩, fun F' hF' hF => ?_⟩
  · rw [Category.assoc, Over.w F]
    exact h.1.w
  · apply Over.OverMorphism.ext
    apply h₁.1.hom_ext
    · exact hF'.trans (h₁.1.lift_fst _ _ _).symm
    · exact (Over.w F').trans (h₁.1.lift_snd _ _ _).symm
  · refine GlobalTheory.Serre.isMonHom_of_mul_comp _ fun T x y => ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
    obtain ⟨Φ₁, hΦ₁⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G₁ G₁' φ₁ h₁ T
    have key : ∀ z : T ⟶ G', Φ₁ (z ≫ F') = Φ z ≫ F := fun z => by
      apply Over.OverMorphism.ext
      rw [hΦ₁, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc, hF']
    apply Φ₁.injective
    rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]

end GlobalTheory.LamF
