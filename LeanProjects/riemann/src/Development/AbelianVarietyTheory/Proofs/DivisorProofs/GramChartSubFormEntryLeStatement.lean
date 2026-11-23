import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramChart_sub_form_entry_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (a b : Fin r), (r : ℝ) * ‖w‖ ≤ 1 → ‖ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Gw X w τ a b - ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.Jd X a b‖ ≤ 3 * ‖w‖ := by
  first | exact @GlobalTheory.GramChartNear.gw_sub_jd_le | exact GlobalTheory.GramChartNear.gw_sub_jd_le | (intros; apply GlobalTheory.GramChartNear.gw_sub_jd_le <;> assumption)
