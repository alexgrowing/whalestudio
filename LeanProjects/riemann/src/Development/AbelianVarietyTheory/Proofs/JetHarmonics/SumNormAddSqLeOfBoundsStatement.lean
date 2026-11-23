import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormAddSqLeOfBounds
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_add_sq_le_add_sq_mul : ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  first | exact @GlobalTheory.sum_norm_add_sq_le_of_bounds | exact GlobalTheory.sum_norm_add_sq_le_of_bounds | (intros; apply GlobalTheory.sum_norm_add_sq_le_of_bounds <;> assumption)
