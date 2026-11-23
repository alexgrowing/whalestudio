import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFormCompactBounds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_form_compact_bounds : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {R : AnRead p σ d} {a : ChartForm p σ d}, IsKaehlerForm R a → ∀ (c : AlgChart p σ d) {Kc : Set (V d)}, IsCompact Kc → Kc ⊆ c.e.target → ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ y ∈ c.e.source, c.e y ∈ Kc → ∀ v : V d, m * ‖v‖ ^ 2 ≤ a c y v.ofLp ∧ a c y v.ofLp ≤ M * ‖v‖ ^ 2 := by
  first | exact @GlobalTheory.KaehlerCmp.exists_bounds | exact GlobalTheory.KaehlerCmp.exists_bounds | (intros; apply GlobalTheory.KaehlerCmp.exists_bounds <;> assumption)
