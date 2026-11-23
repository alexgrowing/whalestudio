import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivIntegralMulKernelApply
import Mathlib
open MeasureTheory Filter Topology Metric
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fderiv_integral_mul_kernel_apply' : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] {U : Set V}, IsOpen U → ∀ {α : V → ℂ}, Continuous α → HasCompactSupport α → tsupport α ⊆ U → ∀ {K : V × V → ℂ}, ContDiffOn ℝ ∞ K (U ×ˢ U) → ∀ {x : V}, x ∈ U → ∀ v : V, fderiv ℝ (fun x' => ∫ y, α y * K (x', y) ∂ν) x v = ∫ y, α y * fderiv ℝ (fun x' => K (x', y)) x v ∂ν := by
  first | exact @GlobalTheory.fderiv_integral_mul_kernel_apply | exact GlobalTheory.fderiv_integral_mul_kernel_apply | (intros; apply GlobalTheory.fderiv_integral_mul_kernel_apply <;> assumption)
