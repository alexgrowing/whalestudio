import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalSubgroupNotMovesUniformBound
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_subgroup_not_moves_uniform_bound : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∃ N : Subgroup G, N.Normal ∧ (∀ σ : G, σ ∈ N ↔ ¬ Moves v ⊤ σ) ∧ ∃ i : ℝ≥0, i < 1 ∧ ∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i := by
  first | exact @GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | exact GlobalTheory.AlmostEt.exists_normal_not_moves_uniform | (intros; apply GlobalTheory.AlmostEt.exists_normal_not_moves_uniform <;> assumption)
