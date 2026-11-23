import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HaarDisintegrationAveragedFibreMeasures
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_disintegration_averagedFibreMeasures : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → (∀ c : K, ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ) → μ {x | q x = 0} = 0 → ∀ φ : V → ENNReal, Measurable φ → ∫⁻ x, φ x ∂μ = ∫⁻ t, ∫⁻ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t) ∂ν := by
  first | exact @GlobalTheory.QuadFibre.disintegration | exact GlobalTheory.QuadFibre.disintegration | (intros; apply GlobalTheory.QuadFibre.disintegration <;> assumption)
