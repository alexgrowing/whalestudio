import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SiegelCover
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_decomposition_mul_int_matrix_of_det_eq_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι], ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, IsSiegel C k a n ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  first | exact @GlobalTheory.ClassFin.siegel_cover | exact GlobalTheory.ClassFin.siegel_cover | (intros; apply GlobalTheory.ClassFin.siegel_cover <;> assumption)
