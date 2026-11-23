import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeProjectionFromLattice
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_projection_from_lattice : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W)
    (F : Submodule ℂ W), Submodule.span ℂ (Set.range P) = ⊤ → Module.finrank ℂ W = 2 * g →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ c : Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ F ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0) →
    ∃ Q : W →ₗ[ℂ] (Fin g → ℂ), LinearMap.ker Q = F ∧ (∀ x, Q (P x) = x) ∧ Module.finrank ℂ F = g := by
  first | exact @GlobalTheory.spanning_map_factors_through_quotient | exact GlobalTheory.spanning_map_factors_through_quotient | (intros; apply GlobalTheory.spanning_map_factors_through_quotient <;> assumption)
