import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CommutingIsometriesCommonEigenvector
import Mathlib
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_isometries_common_eigenvector : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (U : Submodule ℂ V), FiniteDimensional ℂ U → ∀ {ι : Type} (A : ι → V →L[ℂ] V) (x₀ : V), x₀ ∈ U → x₀ ≠ 0 → (∀ i, ∀ x ∈ U, A i x ∈ U) → (∀ i x, ‖A i x‖ = ‖x‖) → (∀ i l x, A i (A l x) = A l (A i x)) → ∃ v ∈ U, ⟪v, x₀⟫_ℂ ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i v = c • v := by
  first | exact @GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry | exact GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry | (intros; apply GlobalTheory.exists_common_eigenvector_inner_ne_zero_of_commute_isometry <;> assumption)
