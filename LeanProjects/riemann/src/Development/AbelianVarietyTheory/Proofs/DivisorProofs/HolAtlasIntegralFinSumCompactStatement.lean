import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompact
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_integral_fin_sum_compact : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.integral (∑ j, α j) = ∑ j, A.integral (α j) := by
  first | exact @GlobalTheory.CxForm.IntegralSum.integral_sum | exact GlobalTheory.CxForm.IntegralSum.integral_sum | (intros; apply GlobalTheory.CxForm.IntegralSum.integral_sum <;> assumption)
