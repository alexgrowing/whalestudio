import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLNonvanishingAtOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_L_nonvanishing_at_one : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  first | exact @GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | exact GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | (intros; apply GlobalTheory.Mem.rayLSeries_entire_ne_zero_one <;> assumption)
