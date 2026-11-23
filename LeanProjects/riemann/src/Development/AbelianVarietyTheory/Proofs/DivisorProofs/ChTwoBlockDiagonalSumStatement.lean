import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoBlockDiagonalSum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
open Matrix Filter Topology GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chTwo_block_diagonal_sum : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] [DecidableEq ι] {μ : ι → ℕ} {H : ∀ τ, E → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} {z : E}, (∀ τ, MContDiffAt 2 (H τ) z) → (∀ τ, IsUnit (H τ z).det) → ∀ ξ₁ η₁ ξ₂ η₂ : E, chTwo (fun x => Matrix.blockDiagonal' fun τ => H τ x) z ξ₁ η₁ ξ₂ η₂ = ∑ τ, chTwo (H τ) z ξ₁ η₁ ξ₂ η₂ := by
  first | exact @GlobalTheory.ChTwoBlockDiag.chTwo_blockDiagonal' | exact GlobalTheory.ChTwoBlockDiag.chTwo_blockDiagonal' | (intros; apply GlobalTheory.ChTwoBlockDiag.chTwo_blockDiagonal' <;> assumption)
