import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartTranslationLift
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactUnitPair
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
theorem _root_.GlobalTheory.T.period_chart_translation_lift : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (A : Over S) [GrpObj A]
    [QuasiSeparated A.hom] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex →
    ∀ v ∈ c.e.target, ∀ (z u : Fin g → ℂ) (hz : (ex (v, z)).1 ≫ A.hom = (ex (v, z + u)).1 ≫ A.hom)
      (W₁ : A.left.Opens) (h : Γ(A.left, W₁)),
      ev _ σ (GlobalTheory.RelCotAb.divMap A ⁻¹ᵁ W₁) ((GlobalTheory.RelCotAb.divMap A).app W₁ h)
          (GlobalTheory.RelCotAb.pairPt A (ex (v, z)) (ex (v, z + u)) hz) =
        ev (A.hom ≫ p) σ W₁ h (ex (v, u)) := by
  first | exact @GlobalTheory.RelCotAb.ev_divMap_pairPt_periodChart | exact GlobalTheory.RelCotAb.ev_divMap_pairPt_periodChart | (intros; apply GlobalTheory.RelCotAb.ev_divMap_pairPt_periodChart <;> assumption)
