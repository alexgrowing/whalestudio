import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneMemOfMulClosedOfDetNeZero
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)), (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | exact GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero | (intros; apply GlobalTheory.one_mem_of_mulClosed_of_det_ne_zero <;> assumption)
