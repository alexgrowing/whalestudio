import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopov
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
open Formalism.REAL Finset Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_capelli_truncated_perelomov_popov : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ, (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) - (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k = r.eval u := by
  first | exact @GlobalTheory.ScalarNewton.scalar_newton | exact GlobalTheory.ScalarNewton.scalar_newton | (intros; apply GlobalTheory.ScalarNewton.scalar_newton <;> assumption)
