import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ErrorFunctionalCoefficientBounded
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.error_functional_coefficient_bounded : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (PP hh : Pol ι N →ₗ[ℝ] ℝ) (vol c : ℝ) (al be : ι → ℝ) (E : Pol ι N), CoefLe E c → (∀ lam, PP (linRoot lam ^ (dimFl ι N + 1)) = vol * (hh (linRoot lam ^ (dimFl ι N + 1)) + ((dimFl ι N : ℝ) + 1) * flagDeg ι N lam * ev lam (invForm j al be)) + ev lam E) → ∃ EE : Pol ι N →ₗ[ℝ] ℝ, (∀ m : (ι × Fin N) →₀ ℕ, m.degree = dimFl ι N + 1 → |EE (monomial m 1)| ≤ c) ∧ ∀ F : Pol ι N, PP F = vol * (hh F - ∑ τ, (al τ - be τ) * shF j τ F - ∑ τ, be τ * totF τ F) + EE F := by
  first | exact @GlobalTheory.FlagPoly.FunctionalForm.functional_form | exact GlobalTheory.FlagPoly.FunctionalForm.functional_form | (intros; apply GlobalTheory.FlagPoly.FunctionalForm.functional_form <;> assumption)
