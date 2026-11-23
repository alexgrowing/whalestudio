import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelImagInverseIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_imag_inverse_identity : ∀ {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (hT : GlobalTheory.IsSiegel T),
    ((T.map fun t => (t.im : ℂ))⁻¹)ᵀ * ((2 : ℂ) • T.map fun t => (t.im : ℂ)) = 2 := by
  first | exact @GlobalTheory.siegel_im_inv_transpose_mul_two | exact GlobalTheory.siegel_im_inv_transpose_mul_two | (intros; apply GlobalTheory.siegel_im_inv_transpose_mul_two <;> assumption)
