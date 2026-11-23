import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingChainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.RingChainExists : GlobalTheory.RingChain.ExistsSt := by
  first | exact @GlobalTheory.RingChain.Exist.existsSt | exact GlobalTheory.RingChain.Exist.existsSt | (intros; apply GlobalTheory.RingChain.Exist.existsSt <;> assumption)
