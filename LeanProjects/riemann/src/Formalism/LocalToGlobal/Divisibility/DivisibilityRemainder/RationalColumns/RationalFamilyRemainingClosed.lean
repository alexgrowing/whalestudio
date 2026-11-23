import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.Divisibility.RecBridgeWire
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.BuRationalOf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.DIV.RatFullFam

open Formalism.L2.Top3 Formalism.L2.Top4

theorem buRat_rrFull_closed (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (selS : SelS 𝒜 sel)
    (selP : BaseLevelCompatibleSelection 𝒜 sel)
    (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selB : SelB 𝒜 sel selS selP selDH selC)
    (hPA : PrimAll sel (selIOf selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, RowsAtSel sel (selIOf selB) (fun Fm hc x hx h i C CH => Formalism.L2.Top4Wire2.DefRowsF (selIOf selB) Fm hc x hx h i C CH) (OneMapOf selB)
        Fm (d3_a hc) CH) :
    Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) ∧
        (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull) :=
  rRows.imp fun Fm CH _ h hc _ _ => by
    obtain ⟨C, _, x0, H⟩ := h hc
    have key : ∀ x ≥ max (max x0 (sel Fm (d3_a hc)).1) (Fm.x1 + 1), ∀ i : Fm.Ix x,
        (Fm.D x i).BuRational ∧ (Fm.D x i).RRFull := by
      intro x hx0 i
      have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx0
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx0
      have hx : Fm.x1 < x := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hx0)
      obtain ⟨ra, _⟩ := H x hx hs h0 i
      obtain ⟨prows, hsep⟩ := hPA Fm (d3_a hc) x hx hs i
      have hok1 := (selC Fm (d3_a hc) x hx hs i).ok1
      have hU := Formalism.IndefR.LevelRealisationRankEquality.tupAllUsed_of_real (selB Fm (d3_a hc) x hx hs i).Q
      have hR := (hDivG Fm (d3_a hc) x hx hs i).toRows hU
      have hPt := Formalism.L2.DIV.dcPt_of_G hU (hDcPtG Fm (d3_a hc) x hx hs i)
      have hF := Formalism.L2.DIV.RatFullPt.colFacts_real ((selIOf selB) Fm (d3_a hc) x hx hs i) hok1 hsep prows ra.seeIso ra.miStar
      exact ⟨Formalism.L2.DIV.RatFullPt.buRational_of _ hok1 hF hR hPt (Fm.ties x i).bu_def, Formalism.L2.DIV.RatFullPt.rrFull_of _ hF hR⟩
    exact ⟨⟨_, fun x hx i => (key x hx i).1⟩, ⟨_, fun x hx i => (key x hx i).2⟩⟩

end Formalism.L2.DIV.RatFullFam

end
