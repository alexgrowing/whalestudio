import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChTwoImaginaryPartSymmetricZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
open Matrix Filter Topology GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chTwo_imaginary_part_symmetric_zero : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} {Z : E → Matrix (Fin g) (Fin g) ℂ} {W : Set E} {w : E}, IsOpen W → w ∈ W → (∀ i k, DifferentiableOn ℂ (fun x => Z x i k) W) → (∀ x ∈ W, (Z x).IsSymm) → IsUnit ((Z w).map fun c => ((c.im : ℝ) : ℂ)).det → ∀ ξ₁ η₁ ξ₂ η₂ : E, chTwo (fun x => (Z x).map fun c => ((c.im : ℝ) : ℂ)) w ξ₁ η₁ ξ₂ η₂ = 0 := by
  first | exact @GlobalTheory.ImSymmChTwo.chTwo_im_eq_zero | exact GlobalTheory.ImSymmChTwo.chTwo_im_eq_zero | (intros; apply GlobalTheory.ImSymmChTwo.chTwo_im_eq_zero <;> assumption)
