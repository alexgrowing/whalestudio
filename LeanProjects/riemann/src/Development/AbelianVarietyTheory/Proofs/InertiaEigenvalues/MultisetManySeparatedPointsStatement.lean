import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetManySeparatedPoints
import Mathlib
open Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  first | exact @GlobalTheory.multiset_many_separated_points | exact GlobalTheory.multiset_many_separated_points | (intros; apply GlobalTheory.multiset_many_separated_points <;> assumption)
