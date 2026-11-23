import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.NoColumnCase.LvlWire
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.LinkedMeasures.SlopeId
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.ValueBounds.SlopeMaxB
import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.AdmissibleClasses.LinkGCl
import Formalism.LocalToGlobal.TieTwRecOf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.DIV.RestFinal

open Formalism.L2.Top3

theorem hh_closed {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (CF0 : List ℝ → ℝ)
    (he : Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      DIVinN Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
        (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
          (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      LocalQuadraticParts.ComplementTwoFamily Fm → DIVinN Fm → LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
  Closed.large (Formalism.MainNotions.DIV.Proofs.thrHH Formalism.L2.DIV.SlopeMaxB.EbMu Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH CF0)
    (tie.and ((Formalism.L2.DIV.LinkGCl.linkG_frame 𝒜 sel).and he))
    fun Fm CH hL h hc hTu hDG c2 hN =>
      have hE := Formalism.L2.DIV.LvlWire.lvlF_of_ties Fm h.1 hTu
      have hrk := Formalism.L2.DIV.LvlWire.muRank_of_lvl Fm (by norm_num : (0 : ℝ) < 3)
        (Formalism.L2.DIV.LvlWire.proviso_of_working_class Fm hc) hE hTu
      have lMu := Formalism.SlopeId.linkMu_of_full Fm hTu hDG (Formalism.L2.DIV.LvlWire.nuFullF_of_lvl Fm hE) hrk
      Formalism.L2.DIV.LvlWire.hh_of_lvl Fm CH Formalism.L2.DIV.SlopeMaxB.EbMu CF0 hL hE hTu hrk (h.2.1 hc hTu hDG) lMu c2
        (Formalism.L2.DIV.SlopeMaxB.boundB_of_sel (sel Fm (d3_a hc)) hTu) (h.2.2 hc hTu hDG hN)

theorem remaining_bound_final {𝒜 : FamClass} (Cabs : ℝ) (sel : Formalism.L2.TSel 𝒜) (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (CF0 : List ℝ → ℝ)
    (he : Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      DIVinN Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
        (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
          (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b)
    (br : Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) ∧ (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull)) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm → Formalism.L2.Top4.RemainingDivisionBounds Fm Cabs CH :=
  ((hh_closed sel tie CF0 he).and br).imp fun Fm _ _ h hc hT hD =>
    show Formalism.L2.Top4.RemainingDivisionBounds Fm Cabs _ from { hh := h.1 hc hT hD, bu := (h.2 hc hT hD).1, rr := (h.2 hc hT hD).2, la := Formalism.L2.DIV.Wire.la_of Fm }

end Formalism.L2.DIV.RestFinal

end

section Test
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3 Formalism.L2.Top4
example (𝒜 : FamClass) (Cabs : ℝ) (sel : Formalism.L2.TSel 𝒜) (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm) (CF0 : List ℝ → ℝ)
    (he : Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      DIVinN Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
        (Fm.D x i).div.RR.muMax + Formalism.BasicNotions.DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
          (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b)
    (br : Closed (D3 3 𝒜) fun Fm _ => ∀ _ : D3 3 𝒜 Fm, Formalism.MainNotions.TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) ∧ (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull)) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm → RemainingDivisionBounds Fm Cabs CH :=
  Formalism.L2.DIV.RestFinal.remaining_bound_final Cabs sel tie CF0 he br
end Test
