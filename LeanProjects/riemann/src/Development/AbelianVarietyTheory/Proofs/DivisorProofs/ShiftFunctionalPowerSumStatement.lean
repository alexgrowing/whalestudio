import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalPowerSum
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_functional_power_sum : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j k : ℕ) (Q : Pol ι N) (τ σ : ι), 1 ≤ k → shF j τ (pSum σ k * Q) = (if τ = σ then (k : ℝ) * degFl ι N (pLow j τ (k - 1) * Q) else 0) ∧ totF τ (pSum σ k * Q) = (if τ = σ ∧ k = 1 then (N : ℝ) * degFl ι N Q else 0) := by
  first | exact @GlobalTheory.FlagPoly.shF_totF_pSum_mul | exact GlobalTheory.FlagPoly.shF_totF_pSum_mul | (intros; apply GlobalTheory.FlagPoly.shF_totF_pSum_mul <;> assumption)
