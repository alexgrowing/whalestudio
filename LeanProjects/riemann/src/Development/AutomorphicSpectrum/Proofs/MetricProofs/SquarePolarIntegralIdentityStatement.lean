import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SquarePolarIntegralIdentity
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_polar_integral_identity : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → ∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) = 2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.AnSq.sum_polar_gH_eq | exact GlobalTheory.CompanionTheory.Ar.PB.AnSq.sum_polar_gH_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.AnSq.sum_polar_gH_eq <;> assumption)
