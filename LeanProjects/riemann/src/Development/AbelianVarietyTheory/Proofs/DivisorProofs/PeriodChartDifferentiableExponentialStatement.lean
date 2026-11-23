import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartDifferentiableExponential
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
theorem _root_.GlobalTheory.T.period_chart_differentiable_exponential : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (D' : ℕ) (h' : IsRegVar (A.hom ≫ p) D') (D g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → ∀ P ∈ cov c.e.target g, ∀ x : (h'.atlas σ).Pt, x.pt = ex P → ContinuousAt ex P ∧ DifferentiableAt ℂ (x.ch ∘ ex) P := by
  first | exact @GlobalTheory.TorsionForm.IsPeriodChart.continuousAt_and_differentiableAt | exact GlobalTheory.TorsionForm.IsPeriodChart.continuousAt_and_differentiableAt | (intros; apply GlobalTheory.TorsionForm.IsPeriodChart.continuousAt_and_differentiableAt <;> assumption)
