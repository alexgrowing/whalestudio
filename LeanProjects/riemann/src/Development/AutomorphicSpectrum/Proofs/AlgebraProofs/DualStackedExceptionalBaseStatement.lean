import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalBase
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_base : GroundTheory.Heights₂.Heights.DualStackedExcBase.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exc_base | exact GlobalTheory.CompanionTheory.Ar.Giv.exc_base | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exc_base <;> assumption)
