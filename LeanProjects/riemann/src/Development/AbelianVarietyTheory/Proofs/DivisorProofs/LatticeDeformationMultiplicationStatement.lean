import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeformationMultiplication
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_deformation_multiplication : ∀ (Ω : Type) [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] (g : ℕ) (K : Type) (ρ : K → Fin g → ℂ),
    (∀ a j, starRingEnd ℂ (ρ a j) = ρ a j) → (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ a, ∀ x ∈ Λ, (fun j ↦ ρ a j * x j) ∈ Λ) →
    ∀ (V : Set Ω) (τ : Ω → Λ →+ (Fin g → ℂ)), IsOpen V → (0 : Ω) ∈ V → (∀ x, τ 0 x = x) →
    (∀ x, DifferentiableOn ℂ (fun z ↦ τ z x) V) →
    (∀ z ∈ V, ∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
    ∃ (V' : Set Ω) (D : Ω → (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (ζ : Ω → Fin g → ℂ),
      IsOpen V' ∧ (0 : Ω) ∈ V' ∧ V' ⊆ V ∧ DifferentiableOn ℂ ζ V' ∧ ζ 0 = 0 ∧ (∀ z ∈ V', ∀ j, ‖ζ z j‖ < 1) ∧
      (∀ z ∈ V', ∀ x : Λ, D z (τ z x) = fun j ↦ (x : Fin g → ℂ) j + ζ z j * starRingEnd ℂ ((x : Fin g → ℂ) j)) ∧
      ∀ z ∈ V', ∀ a (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
        (∀ x x' : Λ, (x' : Fin g → ℂ) = (fun j ↦ ρ a j * (x : Fin g → ℂ) j) → τ z x' = M (τ z x)) →
        ∀ w, D z (M w) = fun j ↦ ρ a j * D z w j := by
  first | exact @GlobalTheory.diag_coords_of_holomorphic_lattice_family | exact GlobalTheory.diag_coords_of_holomorphic_lattice_family | (intros; apply GlobalTheory.diag_coords_of_holomorphic_lattice_family <;> assumption)
