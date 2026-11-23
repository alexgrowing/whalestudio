import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZero
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_coeffs_det_sum_smul_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ} (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K), (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  first | exact @GlobalTheory.exists_nat_coeffs_det_ne_zero | exact GlobalTheory.exists_nat_coeffs_det_ne_zero | (intros; apply GlobalTheory.exists_nat_coeffs_det_ne_zero <;> assumption)
