import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Coefficients
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficients' : Coefficients := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Top.coefficients | exact GlobalTheory.CompanionTheory.Ar.PB.Top.coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Top.coefficients <;> assumption)
