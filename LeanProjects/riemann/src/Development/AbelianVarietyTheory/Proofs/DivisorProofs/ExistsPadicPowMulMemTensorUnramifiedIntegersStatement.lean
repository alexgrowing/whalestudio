import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicPowMulMemTensorUnramifiedIntegers
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_pow_mul_mem_tensorUnramifiedIntegers : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) (x : KQ p K r), ∃ k : ℕ, (p : KQ p K r) ^ k * x ∈ intKQ p K r := by
  first | (exact @GlobalTheory.LKRes.exists_pow_mul_mem_intKQ) | (exact GlobalTheory.LKRes.exists_pow_mul_mem_intKQ) | (intros; apply GlobalTheory.LKRes.exists_pow_mul_mem_intKQ  <;> assumption)
