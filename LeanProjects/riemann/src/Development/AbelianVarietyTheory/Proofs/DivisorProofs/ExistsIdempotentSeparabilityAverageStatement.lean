import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSeparabilityAverage
import Mathlib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_separability_average : ∀ (C O : Type) [CommRing C] [Ring O] (I : Ideal C), I ^ 2 = ⊥ → ∀ (N : ℤ) (k : ℕ) (x y : Fin k → O), ∑ j, x j * y j = (N : O) → (∀ c : O, ∑ j, (c * x j) ⊗ₜ[ℤ] y j = ∑ j, x j ⊗ₜ[ℤ] (y j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρ : O →+* Module.End C H) (ε : Module.End C H), ε * ε = ε → (∀ c, ρ c * ε = ε * ρ c) → ∀ F : Submodule C H, I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, ρ c x ∈ F) → (∀ x ∈ F, ε x ∈ F) → (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) → ∃ π : Module.End C H, π * π = π ∧ (∀ c, ρ c * π = π * ρ c) ∧ π * ε = π ∧ ε * π = π ∧ (∀ z, ε z = z → z - π z ∈ F) ∧ (∀ z ∈ F, ε z = z → π z ∈ I • (⊤ : Submodule C H)) := by
  first | exact @GlobalTheory.SepAverage.exists_idempotent_average | exact GlobalTheory.SepAverage.exists_idempotent_average | (intros; apply GlobalTheory.SepAverage.exists_idempotent_average <;> assumption)
