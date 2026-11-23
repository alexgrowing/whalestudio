import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → HasStrictFDerivAt (yF X) (dY X) 0 := by
  first | exact @GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | exact GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | (intros; apply GlobalTheory.SUChartSection.yF_hasStrictFDerivAt <;> assumption)
