import Formalism.SharpRestriction.Divisibility.HookProducts.GaugeFormBoundOfUniformSize
import Formalism.SharpRestriction.Divisibility.SlopeExcess.HeightBoundOfComponentBounds
import Formalism.LocalToGlobal.GlobalTheory.PlacesP

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.HookProductBasics

open Formalism.BasicNotions Formalism.MainNotions

theorem hh_of_inputs {eps : ℝ} (Fm : FamP eps) (CH crystallineComparison : ℝ) (Eb CF0 : List ℝ → ℝ)
    (hL : Fm.Large (Formalism.MainNotions.DIV.Proofs.thrHH Eb Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH CF0) CH)
    (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (hTu : TuSize Fm) (hNF : NuFullF Fm) (hrk : J.MuRank Fm)
    (lG : LinkG Fm) (lMu : LinkMu Fm) (c2 : LocalQuadraticParts.ComplementTwoFamily Fm)
    (hb : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ Eb Fm.cOut * (Fm.L x i).sc.b)
    (he : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) :
    LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
  Formalism.MainNotions.DIV.Proofs.height_bound_of_component_bounds Fm CH Eb Formalism.MainNotions.DIV.HookProducts.Row4C.EcHH CF0 hL
    (Formalism.L2.GlobalTheoryTheory.Places.slope_lemma_division_form Fm crystallineComparison h10 (Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu) hTu hrk lG lMu)
    hrk hNF hb (Formalism.MainNotions.DIV.HookProducts.Row4C.gauge_form_bound_of_uniform_size Fm c2) hTu he

end Formalism.MainNotions.DIV.HookProducts.HookProductBasics

end
