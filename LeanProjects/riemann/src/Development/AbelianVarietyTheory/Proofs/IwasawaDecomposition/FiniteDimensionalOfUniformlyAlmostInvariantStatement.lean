import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfUniformlyAlmostInvariant
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_of_uniformly_almost_invariant_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)), (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K), (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) → FiniteDimensional ℂ E := by
  first | exact @GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | exact GlobalTheory.finiteDimensional_of_uniformly_almost_invariant | (intros; apply GlobalTheory.finiteDimensional_of_uniformly_almost_invariant <;> assumption)
