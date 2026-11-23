import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuum
import Mathlib
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_heisenberg_translates_of_vacuum : ∀ (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M), (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ v, ρ 0 v = v) → (∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v) → (∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1) → (∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x) → (∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u) → e ≠ 0 → (∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) → (∀ u ∈ Λ, ρ (2 • u) e = e) → (∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e) → ∀ v : M, (∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) → v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  first | exact @GlobalTheory.HeisVacuum.mem_span_translates_vacuum | exact GlobalTheory.HeisVacuum.mem_span_translates_vacuum | (intros; apply GlobalTheory.HeisVacuum.mem_span_translates_vacuum <;> assumption)
