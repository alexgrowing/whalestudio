import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointsIntegralProductFormula
import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_points_integral_product_formula : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ) (w : Fin (GroundTheory.Heights₂.Heights.LowerBoundFree.dimFl Ψ N) → Ψ × Fin N), 2 ≤ N → ptsIntegral (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (pot fun r => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w r)) (fun _ => 1) = ((GroundTheory.Heights₂.Heights.LowerBoundFree.flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.borel_word | exact GlobalTheory.CompanionTheory.Ar.Giv.borel_word | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.borel_word <;> assumption)
