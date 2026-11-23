import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormGaussianWeightForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_gaussian_weight_form : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d} {C : TopologicalSpace.Closeds Y} {n : CxPts p σ → ℝ}, IsDivNorm R C n → ∀ (c : AlgChart p σ d) {y : CxPts p σ}, y ∈ c.e.source → ∃ ε > 0, ∃ (g : ReciprocityTheory.L2DbarEstimates.V d → ℂ) (F : ReciprocityTheory.L2DbarEstimates.V d → ℝ) (A : ℝ), 0 ≤ A ∧ ∀ w ∈ Metric.ball (c.e y) ε, w ∈ c.e.target ∧ n (c.e.symm w) ^ 2 = ‖g w‖ ^ 2 * Real.exp (-F w) ∧ |F w| ≤ A ∧ ∀ w' ∈ Metric.ball (c.e y) ε, ‖g w - g w'‖ ≤ A * ‖w - w'‖ := by
  first | exact @GlobalTheory.ShFam.IsDivNorm.exists_ball_lipschitz | exact GlobalTheory.ShFam.IsDivNorm.exists_ball_lipschitz | (intros; apply GlobalTheory.ShFam.IsDivNorm.exists_ball_lipschitz <;> assumption)
