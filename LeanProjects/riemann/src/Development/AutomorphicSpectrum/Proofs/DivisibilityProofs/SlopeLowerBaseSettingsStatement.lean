import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SlopeLowerBaseSettings
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_lower_base_settings : GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement → ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ), T.Proportional → 3 * (N - T.j) + 1 ≤ N → (∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B → ∀ c, T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) → T.SlopeLower II (Ch + Cu / 2) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings | exact GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings <;> assumption)
