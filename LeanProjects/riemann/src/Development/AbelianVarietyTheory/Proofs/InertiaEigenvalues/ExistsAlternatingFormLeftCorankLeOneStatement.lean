import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlternatingFormLeftCorankLeOne
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_alternating_form_left_corank_le_one : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ → ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) → (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x := by
  first | exact @GlobalTheory.AltCorank.exists_alt_corank_le_one | exact GlobalTheory.AltCorank.exists_alt_corank_le_one | (intros; apply GlobalTheory.AltCorank.exists_alt_corank_le_one <;> assumption)
