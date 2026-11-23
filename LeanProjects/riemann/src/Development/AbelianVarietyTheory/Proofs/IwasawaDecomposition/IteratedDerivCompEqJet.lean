import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolSprayApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricSmoothBiholomorphicTransferStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetSmoothOfInvertibleMetricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricJetTransferBiholomorphicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChristoffelTransferBiholomorphicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeodesicJetHolomorphicStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

theorem GlobalTheory.ChernReg.iteratedDeriv_comp_eq_jet : ∀ (d : ℕ) (U U' : Set (ReciprocityTheory.L2DbarEstimates.V d)) (τ : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (b b' : ReciprocityTheory.L2DbarEstimates.V d → Matrix (Fin d) (Fin d) ℂ), IsOpen U → IsOpen U' → DifferentiableOn ℂ τ U → Set.MapsTo τ U U' → (∀ k l, ContDiffOn ℝ ∞ (fun v => b' v k l) U') → (∀ v ∈ U, IsUnit (b v).det) → (∀ v ∈ U', IsUnit (b' v).det) → (∀ v ∈ U, ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V d, (ξ.ofLp ᵥ* b v) ⬝ᵥ star ζ.ofLp = ((fderiv ℂ τ v ξ).ofLp ᵥ* b' (τ v)) ⬝ᵥ star (fderiv ℂ τ v ζ).ofLp) → ∀ z ∈ U, ∀ (ξ : ReciprocityTheory.L2DbarEstimates.V d) (u : ℝ → ReciprocityTheory.L2DbarEstimates.V d), ContDiffAt ℝ ∞ u 0 → (∀ n, iteratedDeriv n u 0 = jet b n (z, ξ)) → ∀ n, iteratedDeriv n (τ ∘ u) 0 = jet b' n (τ z, fderiv ℂ τ z ξ) := by
  intro d U U' τ b b' hU hU' hτ hmap hb' hdet hdet' hcomp z hz ξ u hu hju n
  have hb := GlobalTheory.T.metric_smooth_biholomorphic_transfer d U U' τ b b' hU hτ hmap hb' hcomp
  have hj' := GlobalTheory.T.jet_smooth_of_invertible_metric d U' b' hU' hb' hdet'
  have hj := GlobalTheory.T.jet_smooth_of_invertible_metric d U b hU hb hdet
  have hΓ := GlobalTheory.T.metric_jet_transfer_biholomorphic d U U' τ b b' hU hU' hτ hmap hb hb' hdet hdet' hcomp
  rw [GlobalTheory.T.geodesic_jet_holomorphic d U b τ hU hj hτ z hz ξ u hu hju n]
  exact GlobalTheory.T.christoffel_transfer_biholomorphic d U U' τ b b' hU hU' hτ hmap hj' hΓ n (z, ξ) ⟨hz, trivial⟩
