import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormLowPolyEqNegSumCrossing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_low_poly_eq_neg_sum_crossing : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (τ : ι), (toForm (pLow j τ 1 : Pol ι N) : FormPol ι N) = -∑ s ∈ (crSet ι N j).filter (fun s => s.1 = τ), X s := by
  first | exact @GlobalTheory.FlagCurve.toForm_pLow_one | exact GlobalTheory.FlagCurve.toForm_pLow_one | (intros; apply GlobalTheory.FlagCurve.toForm_pLow_one <;> assumption)
