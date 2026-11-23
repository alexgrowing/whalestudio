import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryFormEqBlockMinusLow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_form_eq_block_minus_low : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (τ : ι), (bcForm τ : FormPol ι N) = blkForm j τ - toForm (pLow j τ 1 : Pol ι N) := by
  first | exact @GlobalTheory.FlagForm.bcForm_eq_blkForm_sub_toForm_pLow | exact GlobalTheory.FlagForm.bcForm_eq_blkForm_sub_toForm_pLow | (intros; apply GlobalTheory.FlagForm.bcForm_eq_blkForm_sub_toForm_pLow <;> assumption)
