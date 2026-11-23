import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixEqOfImDotProductMulVecStarEqOnSpan
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span' : ∀ (g : ℕ) (H H' : Matrix (Fin g) (Fin g) ℂ) (S : Set (Fin g → ℂ)),
    Submodule.span ℝ S = ⊤ →
    (∀ a ∈ S, ∀ b ∈ S, (a ⬝ᵥ H.mulVec (star b)).im = (a ⬝ᵥ H'.mulVec (star b)).im) → H = H' := by
  first | exact @GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span | exact GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span | (intros; apply GlobalTheory.matrix_eq_of_im_dotProduct_mulVec_star_eq_on_span <;> assumption)
