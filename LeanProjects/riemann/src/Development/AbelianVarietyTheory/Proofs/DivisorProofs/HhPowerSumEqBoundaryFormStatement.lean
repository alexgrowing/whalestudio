import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HhPowerSumEqBoundaryForm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.Published Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hh_power_sum_eq_boundary_form : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.ArDegree → ArCalc → RegularAlteration → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (hh : Pol ι N →ₗ[ℝ] ℝ), GlobalTheory.FlagZ.IsHh ι N hh → ∀ (τ : ι) (Q : Pol ι N), hh (pSum τ 2 * Q) = formDeg (bcForm τ * toForm Q) := by
  first | exact @GlobalTheory.FlagForm.pSum_two_eq_bcForm | exact GlobalTheory.FlagForm.pSum_two_eq_bcForm | (intros; apply GlobalTheory.FlagForm.pSum_two_eq_bcForm <;> assumption)
