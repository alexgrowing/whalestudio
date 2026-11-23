import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralPotentialWeightChartLtTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QSPow
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_potentialWeight_chart_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ s0 : ℝ, ∀ s : ℝ, s0 ≤ s → ∫⁻ z, ENNReal.ofReal (kaF X x0 s z) ∂muF X x0 < ⊤ := by
  first | exact @GlobalTheory.ScalarPoin.lintegral_kaF_lt_top | exact GlobalTheory.ScalarPoin.lintegral_kaF_lt_top | (intros; apply GlobalTheory.ScalarPoin.lintegral_kaF_lt_top <;> assumption)
