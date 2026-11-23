import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralWeightsApproxReal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial GlobalTheory.FlagPoly Formalism.DegreeFormula Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_integral_weights_approx_real : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Φ : Pol ι N →ₗ[ℝ] ℝ) (d : ℕ) (lam : ι → Fin N → ℝ), ∃ (u : ℕ → ι → Fin N → ℤ) (c : ℕ → ℝ), (∀ m, 0 < c m) ∧ (∀ m τ (a b : Fin N), lam τ a ≤ lam τ b → u m τ a ≤ u m τ b) ∧ Tendsto (fun m => c m * Φ (linRoot (fun τ i => (u m τ i : ℝ)) ^ d)) atTop (𝓝 (Φ (linRoot lam ^ d))) := by
  first | exact @GlobalTheory.WeightApprox.approx | exact GlobalTheory.WeightApprox.approx | (intros; apply GlobalTheory.WeightApprox.approx <;> assumption)
