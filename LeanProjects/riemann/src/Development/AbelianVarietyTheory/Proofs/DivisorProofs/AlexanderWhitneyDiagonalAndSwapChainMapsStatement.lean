import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyDiagonalAndSwapChainMaps
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps : ∀ N, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) ∧ Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) := by
  first | exact @GlobalTheory.EtC.AWChain.aw_wa_chain | exact GlobalTheory.EtC.AWChain.aw_wa_chain | (intros; apply GlobalTheory.EtC.AWChain.aw_wa_chain <;> assumption)
