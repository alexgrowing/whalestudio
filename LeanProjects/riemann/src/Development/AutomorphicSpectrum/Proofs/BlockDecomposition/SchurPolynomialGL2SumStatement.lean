import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurPolynomialGL2Sum
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_polynomial_GL2_sum : ∀ (x y : ℂˣ) (A D : ℤ), D ≤ A → Spherical.evalAt ![x, y] (Spherical.schur ![A, D]) = ∑ j ∈ Finset.Icc D A, (x : ℂ) ^ (A + D - j) * (y : ℂ) ^ j := by
  first | exact @GlobalTheory.CompanionTheory.WS.SchurTwo.evalAt_schur_two | exact GlobalTheory.CompanionTheory.WS.SchurTwo.evalAt_schur_two | (intros; apply GlobalTheory.CompanionTheory.WS.SchurTwo.evalAt_schur_two <;> assumption)
