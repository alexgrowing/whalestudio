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

namespace GlobalTheory.TorsionForm

theorem continuousAt_of_isHolTo_cxPts {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : Type} [CommRing k]
    {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {B : Set E} {y : E → CxPts q σ}
    (H : IsHolTo B fun b => (y b).1) {b : E} (hb : b ∈ B) : ContinuousAt y b := by
  refine tendsto_subtype_rng.2 (Points.tendsto_iff.2 fun U hU => ?_)
  have hn := (H U 0).1.mem_nhds (show b ∈ _ from ⟨hb, hU⟩)
  exact ⟨Filter.mem_of_superset hn fun _ h => h.2, fun f => ((H U f).2.continuousOn.continuousAt hn)⟩

theorem differentiableAt_algChart_of_isHolTo {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : Type}
    [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {B : Set E} {y : E → CxPts q σ}
    (H : IsHolTo B fun b => (y b).1) {b : E} (hb : b ∈ B) {n : ℕ} (c : AlgChart q σ n)
    (hc : y b ∈ c.e.source) : DifferentiableAt ℂ (c.e ∘ y) b := by
  have hs : ∀ᶠ b' in nhds b, y b' ∈ c.e.source :=
    (continuousAt_of_isHolTo_cxPts H hb).eventually (c.e.open_source.mem_nhds hc)
  refine differentiableAt_euclidean.2 fun a => ?_
  have hn := (H c.U 0).1.mem_nhds (show b ∈ _ from ⟨hb, c.source_subset hc⟩)
  refine ((H c.U (c.x a)).2.differentiableAt hn).congr_of_eventuallyEq ?_
  filter_upwards [hs] with b' hb' using c.apply_eq _ hb' a

theorem IsPeriodChart.continuousAt_and_differentiableAt :
    ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (A : Over S) [GrpObj A] (D' : ℕ) (h' : IsRegVar (A.hom ≫ p) D') (D g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → ∀ P ∈ cov c.e.target g, ∀ x : (h'.atlas σ).Pt, x.pt = ex P → ContinuousAt ex P ∧ DifferentiableAt ℂ (x.ch ∘ ex) P := by
  intro k _ S p A _ D' h' D g w σ c τ ex H P hP x hx
  refine ⟨continuousAt_of_isHolTo_cxPts H.2.1 hP, ?_⟩
  exact differentiableAt_algChart_of_isHolTo H.2.1 hP (x.1.1 : AlgChart (A.hom ≫ p) σ D') (hx ▸ x.2)

end GlobalTheory.TorsionForm
