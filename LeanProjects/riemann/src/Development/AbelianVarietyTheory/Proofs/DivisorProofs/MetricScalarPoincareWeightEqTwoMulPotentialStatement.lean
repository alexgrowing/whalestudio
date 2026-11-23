import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricScalarPoincareWeightEqTwoMulPotential
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 → phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  first | exact @GlobalTheory.ScalarPoin.phla_laS_cpt | exact GlobalTheory.ScalarPoin.phla_laS_cpt | (intros; apply GlobalTheory.ScalarPoin.phla_laS_cpt <;> assumption)
