import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumDecompositionHomogeneous
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_sum_decomposition_homogeneous : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Pol ι N), F.IsHomogeneous (dimFl ι N + 1) → ∃ Q : ι → ℕ → Pol ι N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl ι N + 1 - k)) ∧ F = ∑ τ : ι, ∑ k ∈ Finset.Icc 1 N, pSum τ k * Q τ k := by
  first | exact @GlobalTheory.FlagPoly.CoinvTop.exists_eq_sum_pSum_mul_of_isHomogeneous | exact GlobalTheory.FlagPoly.CoinvTop.exists_eq_sum_pSum_mul_of_isHomogeneous | (intros; apply GlobalTheory.FlagPoly.CoinvTop.exists_eq_sum_pSum_mul_of_isHomogeneous <;> assumption)
