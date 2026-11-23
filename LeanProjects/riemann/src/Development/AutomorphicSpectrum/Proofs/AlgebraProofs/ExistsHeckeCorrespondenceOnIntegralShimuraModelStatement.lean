import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureCut.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | exact GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | (intros; apply GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut <;> assumption)
