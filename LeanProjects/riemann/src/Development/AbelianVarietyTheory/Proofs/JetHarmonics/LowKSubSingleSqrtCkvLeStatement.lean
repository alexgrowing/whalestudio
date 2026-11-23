import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LowKSubSingleSqrtCkvLe
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowK_sub_single_sqrt_ckv_le : ∀ (n kk : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ) (s : Fin n), Shape ε kk μ bv → lowK ε (μ - Pi.single s 1) = lowK ε μ - Pi.single s 1 ∧ Real.sqrt (ckv ε (lowK ε μ)) + Real.sqrt n ≤ Real.sqrt (ckv ε (lowK ε (μ - Pi.single s 1))) + 8 * n := by
  first | exact @GlobalTheory.lowK_sub_single_and_sqrt_ckv_le | exact GlobalTheory.lowK_sub_single_and_sqrt_ckv_le | (intros; apply GlobalTheory.lowK_sub_single_and_sqrt_ckv_le <;> assumption)
