import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_close_of_pow_reduces_one : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K] [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 → ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  first | exact @GlobalTheory.exists_root_of_unity_close_of_pow_close | exact GlobalTheory.exists_root_of_unity_close_of_pow_close | (intros; apply GlobalTheory.exists_root_of_unity_close_of_pow_close <;> assumption)
