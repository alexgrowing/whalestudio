import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityMovesIntegersOfNeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almostPurity_moves_integers_of_ne_one : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → 0 < v (p : L) → v (p : L) < 1 → ∀ (G : Type) [Group G] [MulSemiringAction G L] [Finite G] [FaithfulSMul G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) → ApproxRoot p v (Fix L (⊤ : Subgroup G)) → ∀ σ : G, σ ≠ 1 → Moves v ⊤ σ := by
  first | exact @GlobalTheory.AlmostEt.moves_of_ne_one | exact GlobalTheory.AlmostEt.moves_of_ne_one | (intros; apply GlobalTheory.AlmostEt.moves_of_ne_one <;> assumption)
