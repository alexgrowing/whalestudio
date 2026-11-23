import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSqInverseTransposeRev
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_sq_inverse_transpose_rev : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), M.PosDef → ∀ i : Fin n, GlobalTheory.GradedNorm.grSq ((M⁻¹)ᵀ.submatrix Fin.rev Fin.rev) (Fin.rev i) = (GlobalTheory.GradedNorm.grSq M i)⁻¹ := by
  first | exact @GlobalTheory.grSq_inv_transpose_rev | exact GlobalTheory.grSq_inv_transpose_rev | (intros; apply GlobalTheory.grSq_inv_transpose_rev <;> assumption)
