import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureBallEqLintegralUpperMeasureDensity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  first | exact @GlobalTheory.measure_ball_eq_lintegral_upperDens | exact GlobalTheory.measure_ball_eq_lintegral_upperDens | (intros; apply GlobalTheory.measure_ball_eq_lintegral_upperDens <;> assumption)
