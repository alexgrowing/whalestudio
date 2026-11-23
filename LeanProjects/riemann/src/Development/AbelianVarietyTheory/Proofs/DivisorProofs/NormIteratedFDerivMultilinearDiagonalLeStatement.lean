import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivMultilinearDiagonalLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ) (i : ℕ) (y : E),
    ‖iteratedFDeriv ℝ i (fun y : E => f (fun _ => y)) y‖ ≤ (j.descFactorial i : ℝ) * ‖f‖ * ‖y‖ ^ (j - i) := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le | exact GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le | (intros; apply GlobalTheory.norm_iteratedFDeriv_diag_multilinear_le <;> assumption)
