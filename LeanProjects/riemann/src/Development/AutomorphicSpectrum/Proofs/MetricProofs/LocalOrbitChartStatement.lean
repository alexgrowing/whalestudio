import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLocalOrbitChart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_orbit_chart_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.LocalOrbitChart.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | exact GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.localOrbitChart <;> assumption)
