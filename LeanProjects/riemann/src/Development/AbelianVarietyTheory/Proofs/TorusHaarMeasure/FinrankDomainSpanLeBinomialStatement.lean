import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinrankDomainSpanLeBinomial
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_domain_span_le_binomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), FiniteDimensional ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ∧ Module.finrank ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) := by
  first | exact @GlobalTheory.UpTie.finrank_domSpan_le | exact GlobalTheory.UpTie.finrank_domSpan_le | (intros; apply GlobalTheory.UpTie.finrank_domSpan_le <;> assumption)
