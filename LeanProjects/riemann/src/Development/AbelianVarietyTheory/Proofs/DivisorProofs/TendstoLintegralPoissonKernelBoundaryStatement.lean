import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLintegralPoissonKernelBoundary
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_lintegral_poisson_kernel_boundary : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  first | exact @GlobalTheory.tendsto_lintegral_concKernel_mul_zero | exact GlobalTheory.tendsto_lintegral_concKernel_mul_zero | (intros; apply GlobalTheory.tendsto_lintegral_concKernel_mul_zero <;> assumption)
