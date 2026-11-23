import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HermitianLogTraceSqFirstVariationBound
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_log_trace_sq_first_variation_bound : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H A : Matrix ι ι ℂ), IsLog H A → ∃ C δ : ℝ, 0 < δ ∧ ∀ Y H' : Matrix ι ι ℂ, (∀ i j, ‖Y i j‖ ≤ δ) → IsLog H' (A + Y) → (Matrix.trace (H' * H')).re ≤ (Matrix.trace (H * H)).re + 2 * (Matrix.trace (H * A⁻¹ * Y)).re + C * ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  first | exact @GlobalTheory.ClassFin.LogSqVar.first_variation | exact GlobalTheory.ClassFin.LogSqVar.first_variation | (intros; apply GlobalTheory.ClassFin.LogSqVar.first_variation <;> assumption)
