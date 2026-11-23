import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationByDiscriminantMultiple
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approximation_by_discriminant_multiple : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ), 1 ≤ j → j < N → ∃ C : ℝ, 0 < C ∧ ∀ (P h : Pol ι N) (vol e : ℝ), 0 < vol → 0 ≤ e → P.IsHomogeneous (dimFl ι N + 1) → h.IsHomogeneous (dimFl ι N + 1) → AntiL j (P - MvPolynomial.C vol * h) → (∀ τ lam, Dom lam → GapZero j τ lam → ev lam h = 0) → (∀ τ, ∀ lam ∈ wallSet (N := N) j τ (1 / (4 * (N : ℝ))), |ev lam P| ≤ e) → ∃ (al be : ι → ℝ) (E : Pol ι N), E.IsHomogeneous (dimFl ι N + 1) ∧ CoefLe E (C * e) ∧ ∀ lam, ev lam P = vol * (ev lam h + ((dimFl ι N : ℝ) + 1) * flagDeg ι N lam * ev lam (invForm j al be)) + ev lam E := by
  first | exact @GlobalTheory.FlagPoly.near_flagDeg_mul_invForm_of_wall_bound | exact GlobalTheory.FlagPoly.near_flagDeg_mul_invForm_of_wall_bound | (intros; apply GlobalTheory.FlagPoly.near_flagDeg_mul_invForm_of_wall_bound <;> assumption)
