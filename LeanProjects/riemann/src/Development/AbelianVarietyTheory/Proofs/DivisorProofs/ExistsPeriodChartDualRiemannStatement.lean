import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodChartDualRiemann
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorsionForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_period_chart_dual_riemann : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S)
    (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ (σ : k →+* ℂ) (y : CxPts p σ),
    ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
      (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ),
      y ∈ c.e.source ∧ Convex ℝ c.e.target ∧ IsPeriodChart h c τ ex := by
  first | exact @GlobalTheory.PeriodChartExists.exists_periodChart | exact GlobalTheory.PeriodChartExists.exists_periodChart | (intros; apply GlobalTheory.PeriodChartExists.exists_periodChart <;> assumption)
