import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSectionOrderFactorisation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_order_factorisation : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsArithVar p 1 → ∀ (σ : k →+* ℂ) (c : AlgChart p σ 1) (W : X.Opens) (f : Γ(X, W)), f ≠ 0 → ∀ (y : CxPts p σ), y ∈ c.e.source → ∀ hW : y.pt ∈ W, ∃ u : ReciprocityTheory.L2DbarEstimates.V 1 → ℂ, (∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ u v) ∧ u (c.e y) ≠ 0 ∧ ∀ᶠ v in 𝓝 (c.e y), ev p σ W f (c.e.symm v) = u v * (v 0 - c.e y 0) ^ germOrd f hW := by
  first | exact @GlobalTheory.LocForm.locForm | exact GlobalTheory.LocForm.locForm | (intros; apply GlobalTheory.LocForm.locForm <;> assumption)
