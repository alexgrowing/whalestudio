import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraSpanned
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_algebra_spanned : ∀ {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ), A.det ≠ 0 → ∀ v : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ, LinearIndependent ℝ v → (∀ i, (v i)ᵀ * A + A * (v i).map (starRingEnd ℂ) = 0 ∧ (v i).trace = 0) → ∀ Y : Matrix (Fin r) (Fin r) ℂ, Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0 → Y.trace = 0 → Y ∈ Submodule.span ℝ (Set.range v) := by
  first | exact @GlobalTheory.TracelessSkewSpan.mem_span_of_linearIndependent | exact GlobalTheory.TracelessSkewSpan.mem_span_of_linearIndependent | (intros; apply GlobalTheory.TracelessSkewSpan.mem_span_of_linearIndependent <;> assumption)
