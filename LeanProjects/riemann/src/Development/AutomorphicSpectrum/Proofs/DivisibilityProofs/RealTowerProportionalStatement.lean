import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportional
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_proportional : PB.Proportional → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (R : RealTower T), R.Unif → T.Proportional := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif | exact GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.rootTower_proportional_of_unif <;> assumption)
