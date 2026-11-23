import Mathlib

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate

namespace GlobalTheory.FibCos

def nrm (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  (G 0 0 + x * G 1 0 + conj x * G 0 1 + ((‖x‖ ^ 2 : ℝ) : ℂ) * G 1 1).re

def cos (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  ‖G 0 0 + x * G 1 0‖ ^ 2 / ((G 0 0).re * nrm G x)

def fs (G : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) : ℝ :=
  G.det.re / (Real.pi * nrm G x ^ 2)

end GlobalTheory.FibCos
