import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegrableContinuousOnAveragedFibreIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → (∀ t : K, t ≠ 0 → Integrable φ (GlobalTheory.QuadFibre.fibOf μ ν q U s t)) ∧ ContinuousOn (fun t => ∫ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  first | exact @GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | exact GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | (intros; apply GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf <;> assumption)
