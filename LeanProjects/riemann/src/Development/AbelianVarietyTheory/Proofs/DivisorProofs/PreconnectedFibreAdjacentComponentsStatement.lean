import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedFibreAdjacentComponents
import Mathlib

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preconnected_fibre_adjacent_components : ∀ (T : Type) [TopologicalSpace T] (S : Set T) (W : Finset T) (e : T → ℚ), _root_.IsPreconnected S →
    (∀ w ∈ W, closure {w} ⊆ S) → (∀ x ∈ S, ∃ w ∈ W, x ∈ closure {w}) → (∀ w ∈ W, 0 ≤ e w) →
    (∃ w ∈ W, e w = 0) → (∃ w ∈ W, 0 < e w) →
      ∃ i ∈ W, ∃ k ∈ W, e i = 0 ∧ 0 < e k ∧ (closure {i} ∩ closure {k}).Nonempty := by
  first | exact @GlobalTheory.closure_cover_meeting_pair | exact GlobalTheory.closure_cover_meeting_pair | (intros; apply GlobalTheory.closure_cover_meeting_pair <;> assumption)
