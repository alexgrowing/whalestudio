import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtTraceChartIndep
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extTrace_chart_indep : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} (T : HermSeq A 1 1) (a b : T.κ) (i : A.ι) {v : V n}, v ∈ chartSet T a i ∩ chartSet T b i → extTrace (midIn T a i) v = extTrace (midIn T b i) v := by
  first | exact @GlobalTheory.SecForm.extTrace_midIn_indep | exact GlobalTheory.SecForm.extTrace_midIn_indep | (intros; apply GlobalTheory.SecForm.extTrace_midIn_indep <;> assumption)
