import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CountBindWordShuffleByPositions
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_bind_wordShuffle_by_positions : ∀ (A : Type) [DecidableEq A] (n : ℕ) (w : Fin n → A) (s₁ s₂ : Multiset (List A)), (s₁.bind fun u => s₂.bind fun v => Shuffle.shuffle u v).count (List.ofFn w) = ∑ ε : Fin n → Bool, s₁.count (((List.finRange n).filter fun j => !ε j).map w) * s₂.count (((List.finRange n).filter ε).map w) := by
  first | exact @GlobalTheory.ShufflePositions.count_bind_shuffle | exact GlobalTheory.ShufflePositions.count_bind_shuffle | (intros; apply GlobalTheory.ShufflePositions.count_bind_shuffle <;> assumption)
