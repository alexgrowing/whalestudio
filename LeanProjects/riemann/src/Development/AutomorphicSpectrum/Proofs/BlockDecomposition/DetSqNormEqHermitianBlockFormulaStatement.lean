import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetSqNormEqHermitianBlockFormula
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_sq_norm_eq_hermitian_block_formula : ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ), ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ → tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) → g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det → ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 * (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | exact GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | (intros; apply GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq <;> assumption)
