import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterIntegralSmooth
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_integral_smooth : ∀ (d : ℕ) (U' C : Set (Fin d → ℂ)) (K : (Fin d → ℂ) × (Fin d → ℂ) → ℝ) (ψ : (Fin d → ℂ) → ℝ), IsOpen U' → IsCompact C → (∀ z ∈ U', ∀ w, w ∉ C → K (z, w) = 0) → MeasureTheory.IntegrableOn ψ C MeasureTheory.volume → ContDiffOn ℝ ∞ K (U' ×ˢ Set.univ) → ContDiffOn ℝ ∞ (fun z => ∫ w, ψ w * K (z, w)) U' := by
  first | exact @GlobalTheory.contDiffOn_integral_mul_kernel_of_compact | exact GlobalTheory.contDiffOn_integral_mul_kernel_of_compact | (intros; apply GlobalTheory.contDiffOn_integral_mul_kernel_of_compact <;> assumption)
