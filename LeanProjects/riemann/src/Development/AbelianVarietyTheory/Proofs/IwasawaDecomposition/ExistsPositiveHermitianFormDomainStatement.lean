import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPositiveHermitianFormDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_hermitian_form_domain : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s), ∃ a : Pt D.what₂.Tau j (N - j) → Pt D.what₂.Tau j (N - j) →ₗ[ℂ] Pt D.what₂.Tau j (N - j) →ₗ⋆[ℂ] ℂ, (∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ ζ, a z ζ ξ = starRingEnd ℂ (a z ξ ζ)) ∧ (∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ ξ, ξ ≠ 0 → 0 < (a z ξ ξ).re) ∧ (∀ ξ ζ, HodgeDomain.SmoothOn fun z => a z ξ ζ) ∧ ∀ W φ, IsPotential (manifold s.T.Z κ.σ₀) (x.kae κ.σ₀) W φ → ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ W → ∀ ξ, (a z ξ ξ).re = ddc (φ ∘ s.toCpt L k) z ξ := by
  first | exact @GlobalTheory.KaePull.kae_pull | exact GlobalTheory.KaePull.kae_pull | (intros; apply GlobalTheory.KaePull.kae_pull <;> assumption)
