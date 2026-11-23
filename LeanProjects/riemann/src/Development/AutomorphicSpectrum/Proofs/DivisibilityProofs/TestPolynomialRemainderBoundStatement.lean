import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialRemainderBound
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_polynomial_remainder_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (Q : Ψ → ℕ → RP Ψ N), 1 ≤ j → j < N → 4 * Fintype.card Ψ * N ^ 2 ≤ B₀ → IsDecomp (testPoly j) Q → |∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum j bad frob B₀ τ k (Q τ k)| ≤ 1.6 * (((dimX Ψ N j : ℝ) + 1) * testDeg Ψ N j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.testRest_bound | exact GlobalTheory.CompanionTheory.Ar.Top.testRest_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.testRest_bound <;> assumption)
