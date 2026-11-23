import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_sum_leibniz : ∀ {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}, (∀ i, DifferentiableAt ℝ (c i) v) → (∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) → dbarAt (fun x => ∑ i, c i x • F i x) v = ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  first | exact @GlobalTheory.CxForm.dbarAt_sum_smul | exact GlobalTheory.CxForm.dbarAt_sum_smul | (intros; apply GlobalTheory.CxForm.dbarAt_sum_smul <;> assumption)
