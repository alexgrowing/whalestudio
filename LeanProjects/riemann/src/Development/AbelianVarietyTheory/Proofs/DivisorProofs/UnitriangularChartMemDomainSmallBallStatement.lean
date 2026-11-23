import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBall
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangularChart_mem_domain_small_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → cpt X x z ∈ X.dom := by
  first | exact @GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le | exact GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le | (intros; apply GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le <;> assumption)
