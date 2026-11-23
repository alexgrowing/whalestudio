import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalChart
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_chart : GroundTheory.Heights₂.Heights.DualStackedExcChart.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart | exact GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.dualStackedExcChart <;> assumption)
