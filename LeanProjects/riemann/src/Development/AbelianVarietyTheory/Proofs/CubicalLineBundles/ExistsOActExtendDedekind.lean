import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AbelianSchemeHomExtendsDedekindOfIsGrpPullbackAlStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_oAct_extend_dedekind : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (O : Type) [CommRing O] (G : Over (Sp R)) [GrpObj G] (G₀ : Over (Sp K)) [GrpObj G₀] (φ : G₀.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → ∀ a₀ : OAct O G₀, ∃ a : OAct O G, ∀ c, (a₀.act c).left ≫ φ = φ ≫ (a.act c).left := by
  intro H R K _ _ _ _ _ O _ G _ G₀ _ φ hG hφ a₀
  have key := fun c => GlobalTheory.T.abelianScheme_hom_extends_dedekind_of_isGrpPullback_alt H R K G G G₀ G₀ φ φ hG hG hφ hφ (a₀.act c) (a₀.hom c)
  choose F hF hc hu using key
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, hc⟩
  · refine (hu 1 (𝟙 G) ?_).symm
    rw [a₀.one]
    simp
  · intro a b
    refine (hu (a * b) (F a ≫ F b) ?_).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, Category.assoc, hc b, ← Category.assoc, hc a, Category.assoc]
  · intro a b
    refine (hu (a + b) (F a * F b) ?_).symm
    let ψ : Over.mk (G₀.hom ≫ spMap (algebraMap R K)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 G₀ (a₀.act a) (a₀.act b) (ψ ≫ F a) (ψ ≫ F b) (hc a).symm (hc b).symm
    rw [a₀.add, ← h, ← MonObj.comp_mul]
    rfl

end GlobalTheory.CM
