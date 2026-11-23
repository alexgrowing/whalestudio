import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartTransitionHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0 dflat herm)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas IsType IsReal Alt delAt dbarAt)
open GlobalTheory.ConjChart (conjCoord conjPts conjChart)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_chart_transition_holomorphic : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (D : ℕ) (c c' : AlgChart p σ D) (τ τ' : V D → Matrix (Fin g) (Fin g) ℂ) (ex ex' : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsPeriodChart w c' τ' ex' → ∀ P ∈ cov c.e.target g, ∀ ψ : Pt (V D) g → Pt (V D) g, DifferentiableAt ℂ ψ P → (∀ᶠ Q in 𝓝 P, ContinuousAt ψ Q ∧ ψ Q ∈ cov c'.e.target g ∧ ex' (ψ Q) = ex Q) → ∀ u : Pt (V D) g, dflat τ P u = 0 → dflat τ' (ψ P) (fderiv ℂ ψ P u) = 0 := by
  first | exact @GlobalTheory.HorizontalChange.dflat_change_eq_zero | exact GlobalTheory.HorizontalChange.dflat_change_eq_zero | (intros; apply GlobalTheory.HorizontalChange.dflat_change_eq_zero <;> assumption)
