import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoboundaryIntegralLawRespectsSimeq
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_integral_law_respects_simeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  first | exact @GlobalTheory.CobSimeqProof.cobSimeq | exact GlobalTheory.CobSimeqProof.cobSimeq | (intros; apply GlobalTheory.CobSimeqProof.cobSimeq <;> assumption)
