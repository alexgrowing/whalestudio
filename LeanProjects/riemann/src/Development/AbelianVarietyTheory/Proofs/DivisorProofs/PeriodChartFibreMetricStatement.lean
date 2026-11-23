import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFibreMetric
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_chart_fibre_metric : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ φ : (Scheme.Modules.pullback A.hom).obj (omega A) ≅ relCot A.hom, ∀ (w : VMetric p (omega A) g) (σ : k →+* ℂ), ∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsFibreMetric ((w.pull A.hom rfl).map φ) c.e.target τ ex := by
  first | exact @GlobalTheory.RelCotAb.relCot_isFibreMetric | exact GlobalTheory.RelCotAb.relCot_isFibreMetric | (intros; apply GlobalTheory.RelCotAb.relCot_isFibreMetric <;> assumption)
