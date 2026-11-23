import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableChartAbsDensity
import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_chartAbsDensity : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : MvPolynomial (Fin n) ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R C : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A → f ∉ J →
    (∀ i, GroundTheory.Heights₂.Heights.SmoothNear (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (φ i)) →
    Integrable (chartAbsDens J A
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x f‖| + C) φ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log <;> assumption)
