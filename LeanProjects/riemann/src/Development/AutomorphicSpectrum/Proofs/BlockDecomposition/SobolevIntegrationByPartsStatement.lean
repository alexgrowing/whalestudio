import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_integration_by_parts : PositivityTheory.RgBcC.Fc.IbpSob := by
  first | exact @GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob | exact GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob | (intros; apply GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob <;> assumption)
