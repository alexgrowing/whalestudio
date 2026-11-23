import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormPositiveLogChart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_positive_log_chart : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), DifferentiableOn ℂ lam (logDom n a) → (∀ t ∈ logDom n a, LinearIndependent ℝ (lam t) ∧ Submodule.span ℝ (Set.range (lam t)) = ⊤ ∧ (Hm t).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) z z).re) ∧ (∀ i i', (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) (lam t i) (lam t i')).im = M i i') ∧ ∀ i, ∑ m, ρ i m • lam t m = Pi.single i 1) → (∃ (C : ℝ) (k : ℕ), ∀ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 → (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) → ‖lam t‖ ≤ C * (1 + ‖t‖) ^ k) → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ t ∈ logDom n a, ‖logExp a t‖ ≤ 1 / 2 → (∀ i : Fin n, (i : ℕ) < a → |(t i).im| ≤ Real.pi) → ∀ w : Fin g → ℂ, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) w w).re ≤ C * (1 + ‖t‖) ^ k * ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ C * (1 + ‖t‖) ^ k * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Hm t) w w).re := by
  first | exact @GlobalTheory.hermForm_norm_comparison_of_periods | exact GlobalTheory.hermForm_norm_comparison_of_periods | (intros; apply GlobalTheory.hermForm_norm_comparison_of_periods <;> assumption)
