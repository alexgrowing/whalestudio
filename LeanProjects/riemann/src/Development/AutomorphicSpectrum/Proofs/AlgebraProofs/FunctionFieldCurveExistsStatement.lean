import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_curve_exists : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FF.places_form_curve | exact GlobalTheory.CompanionTheory.Ar.FF.places_form_curve | (intros; apply GlobalTheory.CompanionTheory.Ar.FF.places_form_curve <;> assumption)
