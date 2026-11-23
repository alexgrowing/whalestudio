import Mathlib
import Formalism.PeriodIntegrals.Transference

open Module

namespace PI

def TransferenceKey : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (u : E), 0 < lam →
    (∀ y : E, (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → ‖y‖ < lam →
      ∃ m : ℤ, inner ℝ u y = (m : ℝ)) →
    ∃ l ∈ Λ, ‖u - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2

theorem cover_of_key (h : TransferenceKey) : TransferenceCover := by
  intro E _ _ _ Λ _ _ lam hlam hmin x
  refine h E Λ lam x hlam ?_
  intro y hy hlt
  by_cases hy0 : y = 0
  · exact ⟨0, by simp [hy0]⟩
  · exact absurd (hmin y hy0 hy) (not_le.mpr hlt)

end PI
