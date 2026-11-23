import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelRootIndependent
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_root_independent : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelRootIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootIndep.main | exact GlobalTheory.CompanionTheory.Ar.RootIndep.main | (intros; apply GlobalTheory.CompanionTheory.Ar.RootIndep.main <;> assumption)
