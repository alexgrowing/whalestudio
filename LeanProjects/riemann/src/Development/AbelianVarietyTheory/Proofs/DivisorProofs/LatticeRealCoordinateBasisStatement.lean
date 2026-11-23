import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRealCoordinateBasis
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_real_coordinate_basis : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∃ (n : ℕ) (b : Fin n → Λ) (c : Fin n → (Fin g → ℂ) →ₗ[ℝ] ℝ),
      (∀ v, ∑ i, c i v • ((b i : Λ) : Fin g → ℂ) = v) ∧
      ∀ (φ : Λ →+ (Fin g → ℂ)) (x : Λ), ∑ i, c i (x : Fin g → ℂ) • φ (b i) = φ x := by
  first | exact @GlobalTheory.exists_zlattice_basis_realCoord_integral | exact GlobalTheory.exists_zlattice_basis_realCoord_integral | (intros; apply GlobalTheory.exists_zlattice_basis_realCoord_integral <;> assumption)
