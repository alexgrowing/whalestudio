import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartFormEquation
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
theorem _root_.GlobalTheory.T.period_chart_form_equation : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (h : IsRegVar p D) (A : Over S) [GrpObj A] (D' : ℕ) (h' : IsRegVar (A.hom ≫ p) D') (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ w : VMetric p (omega A) g, (∀ σ (y : CxPts p σ), ∃ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), y ∈ c.e.source ∧ IsPeriodChart w c τ ex) → ∀ (σ : k →+* ℂ) (Ω₀ : (h'.atlas σ).Fld) (κ : (h.atlas σ).Fld), (h'.atlas σ).IsRealForm 1 Ω₀ → (h.atlas σ).IsRealForm 1 κ → (∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsFlatOn h' Ω₀ c.e.target τ ex) → (∀ x, (hermMat (κ x)).PosDef) → ∀ x, (hermMat (fibForm h h' Ω₀ κ x)).PosDef := by
  first | exact @GlobalTheory.TotalPos.fibForm_posDef | exact GlobalTheory.TotalPos.fibForm_posDef | (intros; apply GlobalTheory.TotalPos.fibForm_posDef <;> assumption)
