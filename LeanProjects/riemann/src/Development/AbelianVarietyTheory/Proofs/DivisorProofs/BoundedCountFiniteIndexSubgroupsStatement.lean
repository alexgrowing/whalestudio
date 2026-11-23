import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCountFiniteIndexSubgroups
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_count_finite_index_subgroups : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], ∃ c : ℕ, ∀ M : ℕ, 0 < M →
    ∃ T : Finset (AddSubgroup A), T.card ≤ M ^ c ∧ ∀ H : AddSubgroup A, (∀ x : A, M • x ∈ H) → H ∈ T := by
  first | exact @GlobalTheory.exists_card_subgroups_containing_nsmul_le | exact GlobalTheory.exists_card_subgroups_containing_nsmul_le | (intros; apply GlobalTheory.exists_card_subgroups_containing_nsmul_le <;> assumption)
