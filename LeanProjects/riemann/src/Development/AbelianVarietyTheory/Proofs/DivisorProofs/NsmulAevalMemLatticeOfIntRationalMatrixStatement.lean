import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NsmulAevalMemLatticeOfIntRationalMatrix
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  first | exact @GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | exact GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix | (intros; apply GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix <;> assumption)
