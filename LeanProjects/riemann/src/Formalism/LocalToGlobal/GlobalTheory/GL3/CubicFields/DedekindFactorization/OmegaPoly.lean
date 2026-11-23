import Mathlib

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open Polynomial

def chiD (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

def omegaPoly (d : ℕ) : ℤ[X] := X ^ 2 - X + C (((d + 1) / 4 : ℕ) : ℤ)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
