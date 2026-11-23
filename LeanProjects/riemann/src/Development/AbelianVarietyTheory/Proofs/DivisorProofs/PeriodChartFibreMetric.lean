import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactUnitPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartSectionTrivialisationStatement

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelCotAb

theorem relCot_isFibreMetric : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ φ : (Scheme.Modules.pullback A.hom).obj (omega A) ≅ relCot A.hom, ∀ (w : VMetric p (omega A) g) (σ : k →+* ℂ), ∀ (c : AlgChart p σ D) (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex → IsFibreMetric ((w.pull A.hom rfl).map φ) c.e.target τ ex := by
  intro k _ S p D A _ g hA hs
  haveI := hA.proper
  refine ⟨GlobalTheory.RelCotAb.relCotIso A, fun w σ c τ ex H P hP W F F' hx => ?_⟩
  obtain ⟨v, z⟩ := P
  have hv : v ∈ c.e.target := hP.1
  obtain ⟨h₁, -, -, -, hmet⟩ := H.2.2 v hv
  have hy : Points.PtsOver.map A.hom rfl _ (ex (v, z)) = c.e.symm v := Subtype.ext (h₁ z)
  have hpick := (w.met σ).isVB.mem_pick (c.e.symm v)
  obtain ⟨U, W₁, hxU, hle, ch⟩ := GlobalTheory.Conormal.exists_isChart (GlobalTheory.LieVB.sec_hom η[A]) (mem_ptsIn.1 hpick)
  let c₀ : GlobalTheory.VB.Chart (omega A) g := ⟨U, _, ((w.met σ).isVB.pick (c.e.symm v)).isFrame.res hle⟩
  choose h hh using fun a => ch.d_surjective (GlobalTheory.LieVB.sec_hom η[A]) (c₀.e a)
  have hU : c.e.symm v ∈ ptsIn p σ U := mem_ptsIn.2 hxU
  let C : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i a => cot ex W₁ (h a) v i
  have hG : (w.met σ).G c₀ (c.e.symm v) = HermFrame.chg C ((2 : ℂ) • imPart τ v) := by
    ext a b
    rw [← (w.met σ).form_frame c₀ hU, ← hh, ← hh, HermFrame.chg_apply]
    exact hmet U W₁ ch.le _ _ hU
  have hK := GlobalTheory.T.period_chart_section_trivialisation k S p D A g w σ c τ ex H v z hv c₀ W₁ ch.le h (fun a => (hh a).symm) hU
  have hyc : Points.PtsOver.map A.hom rfl _ (ex (v, z)) ∈ ptsIn p σ c₀.U := hy ▸ hU
  have hxc : ex (v, z) ∈ ptsIn _ σ (c₀.pull w.isVB A.hom).U := hyc
  change (((w.met σ).pull A.hom rfl).map (GlobalTheory.RelCotAb.relCotIso A)).form _ _ _ = _
  rw [Met.form_eq _ ((c₀.pull w.isVB A.hom).map (GlobalTheory.RelCotAb.relCotIso A)) hxc _ _ hx,
    Met.map_G _ _ (c₀.pull w.isVB A.hom) hxc, Met.pull_G _ _ _ c₀ hyc, hy, hG, HermFrame.form_chg, hK W F hx,
    hK W F' hx]

end GlobalTheory.RelCotAb
