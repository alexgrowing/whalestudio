import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RenameSwapAtMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarFlagZ
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.Published Formalism.DegreeFormula

namespace GlobalTheory.FlagForm

theorem pSum_two_eq_bcForm : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.ArDegree → ArCalc → RegularAlteration → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (hh : Pol ι N →ₗ[ℝ] ℝ), GlobalTheory.FlagZ.IsHh ι N hh → ∀ (τ : ι) (Q : Pol ι N), hh (pSum τ 2 * Q) = formDeg (bcForm τ * toForm Q) := by
  intro hP hD hA hR ι _ _ N hh hHh τ Q
  exact GlobalTheory.FlagAnti.eq_formDeg_of_swap hh hHh τ
    (GlobalTheory.FlagSwapDefect.swap_defect hA hR hP hD ι N hh hHh τ) Q

end GlobalTheory.FlagForm
