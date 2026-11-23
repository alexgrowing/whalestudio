import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliIsReduced
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_moduli' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l), IsReduced Xo.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.moduli_isReduced | exact GlobalTheory.CompanionTheory.Ar.moduli_isReduced | (intros; apply GlobalTheory.CompanionTheory.Ar.moduli_isReduced <;> assumption)
