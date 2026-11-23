import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.WeilBound.CoreStatements.SesquilinearFractions.SqrtDiscriminantBoundsCmField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  first | exact @PositivityTheory.Xgf.sqrt_discriminant_bounds_cm_field | exact PositivityTheory.Xgf.sqrt_discriminant_bounds_cm_field
