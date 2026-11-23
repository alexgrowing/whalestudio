import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAevalTraceFormLeFibreValues
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_aeval_traceForm_le_fibreValues : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K → ∀ (B : Subring K) (hB : ∀ l, x l / x 0 ∈ B), (∀ b ∈ B, IsIntegral (ratR x 0) b) → ∀ (w : B) (T : MvPolynomial (Fin (D + 1)) ℤ), (Algebra.trace (ratF x) K (w : K) : K) = aeval (fun l => x l / x 0) T → ∀ (z : Fin (D + 1) → ℂ) (M : ℝ), z 0 = 1 → (∀ φ : B →+* ℂ, (∀ l, φ ⟨x l / x 0, hB l⟩ = z l) → ‖φ w‖ ≤ M) → ‖aeval z T‖ ≤ Module.finrank (ratF x) K * M := by
  first | exact @GlobalTheory.HSAmp.norm_aeval_trace_le | exact GlobalTheory.HSAmp.norm_aeval_trace_le | (intros; apply GlobalTheory.HSAmp.norm_aeval_trace_le <;> assumption)
