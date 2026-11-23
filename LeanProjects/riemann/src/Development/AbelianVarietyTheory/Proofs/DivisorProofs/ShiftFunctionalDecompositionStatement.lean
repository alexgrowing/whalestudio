import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalDecomposition
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_functional_decomposition : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (Q : ι → ℕ → Pol ι N) (τ : ι), 1 ≤ N → shF j τ (∑ σ : ι, ∑ k ∈ Finset.Icc 1 N, pSum σ k * Q σ k) = ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * degFl ι N (pLow j τ (k - 1) * Q τ k) ∧ totF τ (∑ σ : ι, ∑ k ∈ Finset.Icc 1 N, pSum σ k * Q σ k) = (N : ℝ) * degFl ι N (Q τ 1) := by
  first | exact @GlobalTheory.FlagPoly.shF_totF_powerComb | exact GlobalTheory.FlagPoly.shF_totF_powerComb | (intros; apply GlobalTheory.FlagPoly.shF_totF_powerComb <;> assumption)
