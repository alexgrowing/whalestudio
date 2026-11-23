import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IwasawaDecompositionRealMatrix
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_real_matrix : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ g = k * diagonal a * n := by
  first | exact @GlobalTheory.ClassFin.iwasawa_real | exact GlobalTheory.ClassFin.iwasawa_real | (intros; apply GlobalTheory.ClassFin.iwasawa_real <;> assumption)
