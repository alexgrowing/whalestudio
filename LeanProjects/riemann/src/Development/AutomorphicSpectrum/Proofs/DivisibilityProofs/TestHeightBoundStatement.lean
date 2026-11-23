import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestHeightBound
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_height_bound : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd → T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C' rd Lval → T.SlopeLower II C rd Lval → hh (testPoly T.j) ≤ ((dimX Ψ N T.j : ℝ) + 1) * testDeg Ψ N T.j * (Fintype.card Ψ * ((min T.j (N - T.j) : ℕ) / 2 * Real.log (N + 1))) → T.LowerBoundAtBase II hh frob (2 * (C + C') + 3) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.test_height_bound_slope_flat | exact GlobalTheory.CompanionTheory.Ar.Top.test_height_bound_slope_flat | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.test_height_bound_slope_flat <;> assumption)
