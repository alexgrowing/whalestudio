import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_factors_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X → ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint | exact GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint <;> assumption)
