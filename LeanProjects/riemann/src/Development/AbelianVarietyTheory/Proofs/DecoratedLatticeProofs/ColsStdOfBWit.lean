import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem colsStd_of_bWit {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c) (h : Bl.BWit q b) :
    q.w.I.Ok ∧ Nonempty (GlobalTheory.Mem.Col2.TC.Pins q.B q.w.px) ∧ GlobalTheory.Mem.Col2.TC.IsTw q.w.I ∧
      Nonempty (GlobalTheory.Mem.Col2.TC.StdC q.w.I q.w.l q.Z b.R.T.cols) ∧ GlobalTheory.AdForm.TwStd (packB b) := by
  have hs := h.recPin.s
  refine ⟨q.w.ok, ⟨q.w.pins⟩, q.x.pin.isTw, ⟨?_⟩, ?_⟩
  · have e : b.R.T.cols = q.x.col.C := hs.cols
    rw [e]
    exact q.x.col.std
  · obtain ⟨he, hstd⟩ := hs.tw
    exact ⟨q.w.l0, _, he, (eqRec_heq _ _).symm, hstd⟩

end GlobalTheory.Fam
