import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureEqZeroOfFiniteInterLines
import Mathlib
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_eq_zero_of_finite_inter_lines' : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V), MeasurableSet Z → ∀ y : V, (∀ x : V, {t : K | x + t • y ∈ Z}.Finite) → μ Z = 0 := by
  first | exact @GlobalTheory.measure_eq_zero_of_finite_inter_lines | exact GlobalTheory.measure_eq_zero_of_finite_inter_lines | (intros; apply GlobalTheory.measure_eq_zero_of_finite_inter_lines <;> assumption)
