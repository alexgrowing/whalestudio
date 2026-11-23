import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof : GlobalTheory.TypeAsm.FibC := by
  first | exact @GlobalTheory.TypeAsm.FibProof.fibC | exact GlobalTheory.TypeAsm.FibProof.fibC | (intros; apply GlobalTheory.TypeAsm.FibProof.fibC <;> assumption)
