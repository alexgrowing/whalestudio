import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonempty
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_finite_nonempty : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧ {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Comps.finite_nonempty_maximal | exact GlobalTheory.CompanionTheory.Ar.Comps.finite_nonempty_maximal | (intros; apply GlobalTheory.CompanionTheory.Ar.Comps.finite_nonempty_maximal <;> assumption)
