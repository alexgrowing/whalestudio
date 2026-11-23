import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldDegreeEq
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_degree_eq : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.geoNum_one_eq_coordDeg <;> assumption)
