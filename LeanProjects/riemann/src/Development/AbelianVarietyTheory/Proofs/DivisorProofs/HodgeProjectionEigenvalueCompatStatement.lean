import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeProjectionEigenvalueCompat
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_projection_eigenvalue_compat : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W),
    Submodule.span ℂ (Set.range P) = ⊤ → ∀ (Q : W →ₗ[ℂ] (Fin g → ℂ)), (∀ x, Q (P x) = x) →
    ∀ (O : Type) (T : O → Module.End ℂ W) (χ : O → Fin g → ℂ),
    (∀ a (x : Λ), (fun j ↦ χ a j * (x : Fin g → ℂ) j) ∈ Λ) →
    (∀ a (x y : Λ), (y : Fin g → ℂ) = (fun j ↦ χ a j * (x : Fin g → ℂ) j) → T a (P x) = P y) →
    ∀ ψ : O → ℂ, (∀ j, ∃ a, χ a j ≠ ψ a) →
    (⨅ a, Module.End.eigenspace (T a) (ψ a) : Submodule ℂ W) ≤ LinearMap.ker Q := by
  first | exact @GlobalTheory.eigenvector_mem_ker_of_ne_coord_char | exact GlobalTheory.eigenvector_mem_ker_of_ne_coord_char | (intros; apply GlobalTheory.eigenvector_mem_ker_of_ne_coord_char <;> assumption)
