import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField

namespace GlobalTheory.Fc

theorem realTied_setDiv {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (H : Formalism.L2.Theta.RealTied D) : Formalism.L2.Theta.RealTied (setDiv D N h) :=
  ⟨H.cdScale, H.dsig, H.dsig_all, H.vol⟩

theorem built_val (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd) (κ : Par) (D : D7) (O : Obj D) (c : ℝ) (b : Bd D O c)
    (hb : Built Q Lk κ D O c b) :
    Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧ O.L.sc.eps = κ.eps ∧
      (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)} := by
  refine Built.ind (R := fun D O _ _ => Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧
      O.L.sc.eps = κ.eps ∧ (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}) ?_ hb
  intro K β _ _ h0 _ _
  obtain ⟨h1, h2, h3, h4, -⟩ := h0
  rw [← h1, ← h2, ← h3, ← h4]
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact ⟨hv, β.p.pt_canon β.canon, rfl, rfl, congrArg Scale.eps β.sc, β.p.pt.xa.h_eq,
    ⟨realTied_setDiv _ _ β.c.real⟩, ⟨⟨(_, _), hv.Del_eq, hv.eta_eq⟩⟩⟩

end GlobalTheory.Fc
