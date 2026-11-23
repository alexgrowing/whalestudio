import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftTubeDomain
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contour_shift_tube_domain : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
    ∀ H : (ι → ℂ) → ℂ, DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω} →
    (∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2)) →
    ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      (∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I)) =
        ∫ y : ι → ℝ, H (fun i => (x₂ i : ℂ) + (y i : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.tubeShift | exact GlobalTheory.CompanionTheory.EisTube.tubeShift | (intros; apply GlobalTheory.CompanionTheory.EisTube.tubeShift <;> assumption)
