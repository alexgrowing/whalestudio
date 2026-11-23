import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotIntFJUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotIntFJ ν μX μG ρ f z → IsQuotIntFJ ν μX μG ρ f z' → z = z' := by
  first | exact @GlobalTheory.QuotIntFJ.quotIntFJ_unique | exact GlobalTheory.QuotIntFJ.quotIntFJ_unique | (intros; apply GlobalTheory.QuotIntFJ.quotIntFJ_unique <;> assumption)
