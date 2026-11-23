import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SqrtDiscriminantBoundsCmField
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_discriminant_bounds_cm_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 1 ≤ Real.sqrt H.d ∧ Real.sqrt H.d ≤ rootDiscr E := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field | exact GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field | (intros; apply GlobalTheory.CompanionTheory.Relay.sqrt_discriminant_bounds_cm_field <;> assumption)
