import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KaehlerPotentialComparisonDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_potential_comparison_domain : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (a : Pt D.what₂.Tau j (N - j) → Pt D.what₂.Tau j (N - j) →ₗ[ℂ] Pt D.what₂.Tau j (N - j) →ₗ⋆[ℂ] ℂ), (∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ ζ, a z ζ ξ = starRingEnd ℂ (a z ξ ζ)) → (∀ W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ W → ∀ ξ, (a z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ) → (∀ g ∈ gammaU (s.fd k) s.j_le (s.lab L k), ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ ζ, a (moebI g z) (fun t => tanAct (g t) (z t) (ξ t)) (fun t => tanAct (g t) (z t) (ζ t)) = a z ξ ζ) ∧ ∀ i, ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ, 2 * x.m * x.cst * |ddc (fun w => Real.exp 1 - Real.log (x.nrm κ.σ₀ i (s.toCpt L k w) ^ 2)) z ξ| ≤ Real.exp 1 * (a z ξ ξ).re := by
  first | exact @GlobalTheory.KaeLaws.inv_and_bound | exact GlobalTheory.KaeLaws.inv_and_bound | (intros; apply GlobalTheory.KaeLaws.inv_and_bound <;> assumption)
