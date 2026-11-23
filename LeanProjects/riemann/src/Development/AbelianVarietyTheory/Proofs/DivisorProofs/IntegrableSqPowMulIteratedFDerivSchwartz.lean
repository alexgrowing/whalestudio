import Mathlib

open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

theorem integrable_sq_pow_mul_iteratedFDeriv_schwartz
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : SchwartzMap E F) (i j : ℕ) :
    Integrable (fun z => (‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) ^ 2) μ := by
  have hint : Integrable (fun z => ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖) μ :=
    SchwartzMap.integrable_pow_mul_iteratedFDeriv μ f i j
  set C := SchwartzMap.seminorm ℝ i j f
  refine (hint.const_mul C).mono' ?_ ?_
  · exact (hint.aestronglyMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun z => ?_)
    have h0 : 0 ≤ ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖ := by positivity
    have hC : ‖z‖ ^ i * ‖iteratedFDeriv ℝ j f z‖ ≤ C := SchwartzMap.le_seminorm ℝ i j f z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right hC h0

end GlobalTheory
