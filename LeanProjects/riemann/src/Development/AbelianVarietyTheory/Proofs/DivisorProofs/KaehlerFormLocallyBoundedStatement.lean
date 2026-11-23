import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFormLocallyBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_form_locally_bounded : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d} {a : ChartForm p σ d}, IsKaehlerForm R a → ∀ (c : AlgChart p σ d) {y : CxPts p σ}, y ∈ c.e.source → ∃ ε > 0, ∃ B : ℝ, ∀ w ∈ Metric.ball (c.e y) ε, w ∈ c.e.target ∧ ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, a c (c.e.symm w) ξ.ofLp ≤ B * ‖ξ‖ ^ 2 := by
  first | exact @GlobalTheory.ShFam.IsKaehlerForm.bound_ball | exact GlobalTheory.ShFam.IsKaehlerForm.bound_ball | (intros; apply GlobalTheory.ShFam.IsKaehlerForm.bound_ball <;> assumption)
