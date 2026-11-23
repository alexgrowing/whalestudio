import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartLeftInvariantLaplacianOpPowEqIterate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_leftInvariantLaplacianOp_pow_eq_iterate : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (n : ℕ),
    ∀ y ∈ invSet E a, chart ((lapOp E a ^ n) φ).1 g y = (lapF E a)^[n] (chart φ.1 g) y := by
  first | exact @GlobalTheory.HCAlpha.chart_lapOp_pow | exact GlobalTheory.HCAlpha.chart_lapOp_pow | (intros; apply GlobalTheory.HCAlpha.chart_lapOp_pow <;> assumption)
