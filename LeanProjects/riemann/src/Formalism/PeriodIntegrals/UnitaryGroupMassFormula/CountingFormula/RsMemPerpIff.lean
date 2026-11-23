import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PartnerVectorExists

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coord

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem rs_e_mem_X (a : Fin D.R.rS) : F0.e a ∈ F0.X := Submodule.subset_span ⟨a, rfl⟩

theorem rs_hT_e_X (a : Fin D.R.rS) {x : (VS D).V} (hx : x ∈ F0.X) : (VS D).hT (F0.e a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso a b
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem rs_mem_perp_iff' (y : (VS D).V) : y ∈ perpS (VS D) F0.X ↔ ∀ a, (VS D).hT (F0.e a) y = 0 := by
  constructor
  · intro hy a
    exact hy _ (rs_e_mem_X D F0 a)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      exact h b
    | zero => simp
    | add w w' _ _ h1 h2 => simp [h1, h2]
    | smul c w _ h' => simp [h']

theorem rs_X_le_perp : F0.X ≤ perpS (VS D) F0.X := fun x hx =>
  (rs_mem_perp_iff' D F0 x).2 fun a => rs_hT_e_X D F0 a hx

theorem rs_mk_X_zero {x : (VS D).V} (hx : x ∈ F0.X) (hp : x ∈ perpS (VS D) F0.X) :
    (Submodule.Quotient.mk (⟨x, hp⟩ : perpS (VS D) F0.X) : WbQ D F0) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact hx

variable {D F0} {f : Fin D.R.rS → (VS D).V}

theorem rs_hT_f_e (hf : PartnerOK D F0 f) (a b : Fin D.R.rS) :
    (VS D).hT (f a) (F0.e b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
  split_ifs <;> simp

end Coord

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
