import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RemainderBounds.RemainingBoundFinal
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.FunTop
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.RationalFamilyRemainingClosed

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.Pk Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S

namespace Formalism.L2.DIV.RestAll

theorem bRest_all (𝒜 : FamClass) (Cabs : ℝ)
    (sel : Formalism.L2.TSel 𝒜)
    (selS : SelS 𝒜 sel)
    (selP : BaseLevelCompatibleSelection 𝒜 sel)
    (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selB : SelB 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.RowsB (selB Fm hc x hx h i))
    (hPA : PrimAll sel (selIOf selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DcPtG (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, RowsAtSel sel (selIOf selB) (fun Fm hc x hx h i C CH => Formalism.L2.Top4Wire2.DefRowsF (selIOf selB) Fm hc x hx h i C CH) (OneMapOf selB)
        Fm (d3_a hc) CH)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → RemainingDivisionBounds Fm Cabs CH := by
  have hf := Formalism.L2.DIV.FunSharpTop.closed_funSharp_thr 𝒜 sel selS selP selDH selC selB hRB hPA hDivG rRows
    Formalism.L2.DIV.SlopeMaxB.EbMu Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH
  have hh : Closed (D3 3 𝒜) fun Fm CH => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      LocalQuadraticParts.ComplementTwoFamily Fm → DIVinN Fm → LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
    (tie.and ((Formalism.L2.DIV.LinkGCl.linkG_frame 𝒜 sel).and hf)).imp fun Fm CH _ h hc hTu hDG c2 hN => by
      obtain ⟨CF0, hL, he⟩ := h.2.2 hc hTu hDG
      have hE := Formalism.L2.DIV.LvlWire.lvlF_of_ties Fm h.1 hTu
      have hrk := Formalism.L2.DIV.LvlWire.muRank_of_lvl Fm (by norm_num : (0 : ℝ) < 3)
        (Formalism.L2.DIV.LvlWire.proviso_of_working_class Fm hc) hE hTu
      have lMu := Formalism.SlopeId.linkMu_of_full Fm hTu hDG (Formalism.L2.DIV.LvlWire.nuFullF_of_lvl Fm hE) hrk
      exact Formalism.L2.DIV.LvlWire.hh_of_lvl Fm CH Formalism.L2.DIV.SlopeMaxB.EbMu CF0 hL hE hTu hrk (h.2.1 hc hTu hDG) lMu c2
        (Formalism.L2.DIV.SlopeMaxB.boundB_of_sel (sel Fm (d3_a hc)) hTu) (he hN)
  have br := Formalism.L2.DIV.RatFullFam.buRat_rrFull_closed 𝒜 sel selS selP selDH selC selB hPA hDivG hDcPtG rRows
  exact (hh.and br).imp fun Fm _ _ h hc hT hD =>
    show RemainingDivisionBounds Fm Cabs _ from
      { hh := h.1 hc hT hD, bu := (h.2 hc hT hD).1, rr := (h.2 hc hT hD).2, la := Formalism.L2.DIV.Wire.la_of Fm }

end Formalism.L2.DIV.RestAll

end
