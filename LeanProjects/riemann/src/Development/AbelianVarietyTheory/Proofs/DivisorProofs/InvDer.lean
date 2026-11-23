import Mathlib

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LawDer

variable {R : Type} [CommRing R] {d : ℕ}

def atZero (H : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  subst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) R)) fun _ => 0) H

def invDer (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (u : Fin d → R)
    (F : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ i, u i • atZero (pderiv R (Sum.inr i) (subst μ F))

end GlobalTheory.LawDer
