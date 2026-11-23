import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightTestBound
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_test_bound : GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (j : ℕ), 1 ≤ j → j < N → HhTestBound j (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl | exact GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.HhTestProof.hhTestBound_hhFl <;> assumption)
