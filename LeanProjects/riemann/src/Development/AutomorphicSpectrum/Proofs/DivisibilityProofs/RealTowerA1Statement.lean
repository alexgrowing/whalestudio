import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerA1
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_A1 : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → R.Pos → T.A1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower | exact GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower <;> assumption)
