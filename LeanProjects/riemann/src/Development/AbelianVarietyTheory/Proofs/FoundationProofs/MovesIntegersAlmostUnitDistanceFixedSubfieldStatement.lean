import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfield
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movesIntegersAlmostUnitDistance_fixedSubfield : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) → ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  first | exact @GlobalTheory.AlmostEt.moves_fix_of_moves | exact GlobalTheory.AlmostEt.moves_fix_of_moves | (intros; apply GlobalTheory.AlmostEt.moves_fix_of_moves <;> assumption)
