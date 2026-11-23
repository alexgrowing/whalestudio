import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.M2ModelOfCurveBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootLineDeRhamModel_of_curveSemiAbelian : CurveSemiAbelianConjecture → RootLineDeRhamModel := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve | exact GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.m2Model_of_m2Curve <;> assumption)
