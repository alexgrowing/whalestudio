import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDataLinearChart
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
theorem _root_.GlobalTheory.T.riemann_data_linear_chart : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (P : PPAS S)
    (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h → ∀ (σ : k →+* ℂ) (s : CxPts p σ)
    (τ₀ : Matrix (Fin P.g) (Fin P.g) ℂ) (e : (Fin P.g → ℂ) → CxPts (P.A.hom ≫ p) σ),
    τ₀.IsSymm → (τ₀.map Complex.im).PosDef →
    (∀ d : P.RiemannData s.1, ∃ F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ),
      (∀ z, (d.u.ex (F z)).left ≫ d.φ = (e z).1) ∧
      ∀ z w, HermFrame.form d.H (F z) (F w) = GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.herm τ₀ z w) →
    ∀ (U : S.Opens) (W : P.A.left.Opens) (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f f' : Γ(P.A.left, W)),
      s ∈ ptsIn p σ U → (h.met σ).form (dUnit P.A hU f) (dUnit P.A hU f') s =
        HermFrame.form ((2 : ℂ) • τ₀.map fun t => (t.im : ℂ))
          (fun a => fderiv ℂ (fun z => ev (P.A.hom ≫ p) σ W f (e z)) 0 (Pi.single a 1))
          (fun a => fderiv ℂ (fun z => ev (P.A.hom ≫ p) σ W f' (e z)) 0 (Pi.single a 1)) := by
  first | exact @GlobalTheory.PeriodChart.dualRiemann_half_form_eq | exact GlobalTheory.PeriodChart.dualRiemann_half_form_eq | (intros; apply GlobalTheory.PeriodChart.dualRiemann_half_form_eq <;> assumption)
