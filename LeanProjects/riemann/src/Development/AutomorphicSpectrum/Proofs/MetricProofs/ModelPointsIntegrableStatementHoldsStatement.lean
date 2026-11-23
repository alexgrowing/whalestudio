import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_points_integrable_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.ModelPtsIntegrable.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable | exact GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable <;> assumption)
