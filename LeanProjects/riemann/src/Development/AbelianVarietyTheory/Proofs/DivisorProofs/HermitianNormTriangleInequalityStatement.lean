import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianNormTriangleInequality
import Mathlib
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_norm_triangle_inequality : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Hm.PosDef → √(((a + b) ⬝ᵥ Hm.mulVec (star (a + b))).re) ≤ √((a ⬝ᵥ Hm.mulVec (star a)).re) + √((b ⬝ᵥ Hm.mulVec (star b)).re) := by
  first | exact @GlobalTheory.posDef_herm_norm_triangle | exact GlobalTheory.posDef_herm_norm_triangle | (intros; apply GlobalTheory.posDef_herm_norm_triangle <;> assumption)
