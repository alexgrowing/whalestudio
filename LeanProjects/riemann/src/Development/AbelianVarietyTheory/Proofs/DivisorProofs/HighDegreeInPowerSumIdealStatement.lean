import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighDegreeInPowerSumIdeal
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.high_degree_in_power_sum_ideal : ∀ (N d : ℕ) (P : MvPolynomial (Fin N) ℝ), P.IsHomogeneous d → N * (N - 1) / 2 < d → P ∈ Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) := by
  first | exact @GlobalTheory.coinvariant_vanish_above_top_degree | exact GlobalTheory.coinvariant_vanish_above_top_degree | (intros; apply GlobalTheory.coinvariant_vanish_above_top_degree <;> assumption)
