import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main <;> assumption)
