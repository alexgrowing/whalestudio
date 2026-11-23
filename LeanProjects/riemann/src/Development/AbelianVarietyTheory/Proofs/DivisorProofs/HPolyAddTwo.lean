import Mathlib

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial

namespace GlobalTheory.FibLine

def fsDens (x : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)

def lineVec (x : ℂ) : Fin 2 → ℂ := ![1, x]

def qCoef (x : ℂ) (ab : Fin 2 × Fin 2) : ℂ :=
  lineVec x ab.2 * starRingEnd ℂ (lineVec x ab.1) / ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)

def entries {R : Type} (H : Matrix (Fin 2) (Fin 2) R) : Fin 2 × Fin 2 → R := fun ab => H ab.1 ab.2

def qMat {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (x : ℂ) : R :=
  ∑ ab : Fin 2 × Fin 2, qCoef x ab • entries H ab

def fibPow (k : ℕ) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ∑ f : Fin k → Fin 2 × Fin 2, C (∫ x : ℂ, (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) * ∏ i, X (f i)

def hPoly (k : ℕ) : MvPolynomial (Fin 2) ℂ :=
  (Nat.rec (motive := fun _ => MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ) (1, X 0)
    (fun _ p => (p.2, X 0 * p.2 - X 1 * p.1)) k).1

theorem hPoly_zero : hPoly 0 = 1 := rfl

theorem hPoly_one : hPoly 1 = X 0 := rfl

theorem hPoly_add_two (k : ℕ) : hPoly (k + 2) = X 0 * hPoly (k + 1) - X 1 * hPoly k := rfl

def trDet : Fin 2 → MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ![X (0, 0) + X (1, 1), X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)]

end GlobalTheory.FibLine
