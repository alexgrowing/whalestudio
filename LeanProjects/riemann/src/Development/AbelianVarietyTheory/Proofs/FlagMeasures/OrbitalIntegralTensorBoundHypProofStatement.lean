import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralTensorBoundHypProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegralTensorBoundHyp_proof : GlobalTheory.TypeAsm.TensC := by
  first | exact @GlobalTheory.TensHS.tensC_holds | exact GlobalTheory.TensHS.tensC_holds | (intros; apply GlobalTheory.TensHS.tensC_holds <;> assumption)
