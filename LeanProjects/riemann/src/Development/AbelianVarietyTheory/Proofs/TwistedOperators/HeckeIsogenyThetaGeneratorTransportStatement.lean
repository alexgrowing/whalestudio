import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_thetaGenerator_transport : GlobalTheory.HeckePointLaw.ThetaTransportLaw := by
  first | exact @GlobalTheory.ThetaTransport.thetaTransportLaw | exact GlobalTheory.ThetaTransport.thetaTransportLaw | (intros; apply GlobalTheory.ThetaTransport.thetaTransportLaw <;> assumption)
