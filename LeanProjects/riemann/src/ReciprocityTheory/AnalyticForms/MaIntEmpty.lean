import Mathlib

namespace ReciprocityTheory.AnForm

open MeasureTheory

noncomputable section

section Levi

variable {ι : Type*} [Fintype ι]

def levi (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) : ℝ :=
  (fderiv ℝ (fderiv ℝ φ) z w w + fderiv ℝ (fderiv ℝ φ) z (Complex.I • w) (Complex.I • w)) / 4

end Levi

section MongeAmpere

variable {D : ℕ}

def hessC (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j =>
    let H := fderiv ℝ (fderiv ℝ φ) z
    let ei : Fin D → ℂ := Pi.single i 1
    let ej : Fin D → ℂ := Pi.single j 1
    ((H ei ej + H (Complex.I • ei) (Complex.I • ej) : ℝ) +
      Complex.I * ((H ei (Complex.I • ej) - H (Complex.I • ei) ej : ℝ))) / 4

def mdisc (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  (1 / (D.factorial : ℂ)) *
    ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ k ∈ S, A k).det

def maDens (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : ℝ :=
  (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (φ k) z).re

def maInt (φ : Fin D → (Fin D → ℂ) → ℝ) (g : (Fin D → ℂ) → ℝ) (U : Set (Fin D → ℂ)) : ℝ :=
  ∫ z in U, g z * maDens φ z

theorem mdisc_zero (A : Fin 0 → Matrix (Fin 0) (Fin 0) ℂ) : mdisc A = 1 := by
  simp [mdisc]

end MongeAmpere

end

end ReciprocityTheory.AnForm
