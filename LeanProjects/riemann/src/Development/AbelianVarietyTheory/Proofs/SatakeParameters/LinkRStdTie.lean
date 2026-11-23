import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr

noncomputable section

namespace GlobalTheory.Svd.LinkStd

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd

theorem stdTie_of_eq {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) (R' : Formalism.L2.RecT q.O.ex)
    (h : RecPinE q R') {D : D7} {O : Obj D} {c : ℝ} (R : BdRec D O c)
    (e : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), BdRec D O c) = ⟨q.w.D q.Z, q.O, R'⟩) : StdTie D O R.T.ker := by
  cases e
  exact StdTie.intro h.std

theorem linkR_stdTie {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Q : V4.Slot) :
    RowE (Bd := BdRec) Q (LinkR p) fun _ D O _ R => StdTie D O R.T.ker :=
  RowE.of_all fun _ _ _ _ R _ _ hl => by
    obtain ⟨q, R', h, e⟩ := hl
    exact stdTie_of_eq q R' h R e

end GlobalTheory.Svd.LinkStd

end
