import Mathlib

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MatDeriv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}

def dMat (H : E → Matrix (Fin m) (Fin m) ℂ) (w ξ : E) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => fderiv ℝ (fun w' => H w' a b) w ξ

def wirt (H : E → Matrix (Fin m) (Fin m) ℂ) (w ξ : E) : Matrix (Fin m) (Fin m) ℂ :=
  (1 / 2 : ℂ) • (dMat H w ξ - Complex.I • dMat H w (Complex.I • ξ))

end GlobalTheory.MatDeriv
