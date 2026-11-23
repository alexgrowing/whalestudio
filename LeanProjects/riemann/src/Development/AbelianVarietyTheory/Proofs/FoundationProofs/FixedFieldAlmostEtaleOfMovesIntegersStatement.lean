import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegers
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal → N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_moves | exact GlobalTheory.AlmostEt.almostSep_of_moves | (intros; apply GlobalTheory.AlmostEt.almostSep_of_moves <;> assumption)
