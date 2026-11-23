import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerPotentialLocallyIntegrableBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertible
open CategoryTheory AlgebraicGeometry Filter Topology Set MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_potential_locally_integrable_bound : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [CompactSpace (CxPts p σ)] (R : AnRead p σ d) (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ), IsKaehlerForm R a → IsExph a E → (∀ y, ∃ c : AlgChart p σ d, y ∈ c.e.source ∧ MeasureTheory.LocallyIntegrableOn (ψ ∘ c.finChart.symm) c.finChart.target MeasureTheory.volume) → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ y, CxPts.CInfAt (fun z => rho a E ψ z t) y := by
  first | exact @GlobalTheory.ChernReg.RhoSmooth.rho_cInfAt | exact GlobalTheory.ChernReg.RhoSmooth.rho_cInfAt | (intros; apply GlobalTheory.ChernReg.RhoSmooth.rho_cInfAt <;> assumption)
