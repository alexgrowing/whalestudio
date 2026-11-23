import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.CuspBlock

def tripSizes (l d N : ℕ) : Fin 3 → ℕ := ![l, d, N - (l + d)]

theorem tripSizes_sum {l d N : ℕ} (h : l + d ≤ N) : ∑ j, tripSizes l d N j = N := by
  simp only [tripSizes, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  omega

def tripPlace {l d N : ℕ} (h : l + d ≤ N) : (Σ j : Fin 3, Fin (tripSizes l d N j)) ≃ Fin N :=
  finSigmaFinEquiv.trans (finCongr (tripSizes_sum h))

variable (k : Type) [CommRing k]

def midHom (l d N : ℕ) : GL (Fin d) k →* Levi k (fun j : Fin 3 => Fin (tripSizes l d N j)) :=
  MonoidHom.mulSingle (fun j : Fin 3 => GL (Fin (tripSizes l d N j)) k) 1

variable {k} in

def glCast {a b : ℕ} (h : a = b) : GL (Fin a) k →* GL (Fin b) k := h ▸ MonoidHom.id _

@[simp] theorem glCast_rfl {a : ℕ} : glCast (k := k) (rfl : a = a) = MonoidHom.id _ := rfl

end GlobalTheory.CuspBlock
