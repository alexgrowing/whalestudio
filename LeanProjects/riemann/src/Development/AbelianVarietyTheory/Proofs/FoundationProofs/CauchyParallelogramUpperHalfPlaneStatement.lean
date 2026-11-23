import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CauchyParallelogramUpperHalfPlane
open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_segment_eq_parallelogram_sides : ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  first | exact @GlobalTheory.cauchy_parallelogram_upper_half_plane | exact GlobalTheory.cauchy_parallelogram_upper_half_plane | (intros; apply GlobalTheory.cauchy_parallelogram_upper_half_plane <;> assumption)
