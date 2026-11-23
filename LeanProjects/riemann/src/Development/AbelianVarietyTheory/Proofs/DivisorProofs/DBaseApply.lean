import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTorsionFormPoint

set_option autoImplicit false

noncomputable section

open GlobalTheory.TorsionForm

namespace GlobalTheory.TorsionForm.Fibrewise

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

def dBase (β : Fin n → E) (ψ : E → ℂ) (b : E) (w : Ext (n + n + g)) : Ext (n + n + g) :=
  ∑ j, (d10 ψ b (β j) • wedge (dt g j) w + d01 ψ b (β j) • wedge (dtb g j) w)

theorem dBase_apply (β : Fin n → E) (ψ : E → ℂ) (b : E) (w : Ext (n + n + g)) :
    dBase β ψ b w = ∑ j, (d10 ψ b (β j) • wedge (dt g j) w + d01 ψ b (β j) • wedge (dtb g j) w) :=
  rfl

end GlobalTheory.TorsionForm.Fibrewise
