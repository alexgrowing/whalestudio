import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoordsStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitCompsOfIsTowerOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem exists_factor_XF_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X →
      ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  intro E _ _ _ H D l Xo c Y Ω _ ξ hξ
  obtain ⟨K, _, _, n, x, y, ht, -, he⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y _ hξ
  obtain ⟨i, hi⟩ := GlobalTheory.CompanionTheory.Ar.TowerOfTest.factor (y ≫ Y.j) ht.gen ξ he.symm
  exact ⟨Spec.map (CommRingCat.ofHom i) ≫ y, by rw [hi, Category.assoc]⟩

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
