import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAbsPowIntegersFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_abs_pow_integers_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ), -1 < s →
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ < ⊤ := by
  first | exact @GlobalTheory.IntShell.lintegral_int_nabs_rpow_lt_top | exact GlobalTheory.IntShell.lintegral_int_nabs_rpow_lt_top | (intros; apply GlobalTheory.IntShell.lintegral_int_nabs_rpow_lt_top <;> assumption)
