import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogSingularIntegrableDisc
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_singular_integrable_disc : ∀ r : ℝ, r ≤ 1 / 2 → ∫⁻ u in Metric.ball (0 : ℂ) r, ENNReal.ofReal (1 / (‖u‖ ^ 2 * tOf u ^ 2)) < ⊤ := by
  first | exact @GlobalTheory.PoincareDisc.lintegral_ball_lt_top | exact GlobalTheory.PoincareDisc.lintegral_ball_lt_top | (intros; apply GlobalTheory.PoincareDisc.lintegral_ball_lt_top <;> assumption)
