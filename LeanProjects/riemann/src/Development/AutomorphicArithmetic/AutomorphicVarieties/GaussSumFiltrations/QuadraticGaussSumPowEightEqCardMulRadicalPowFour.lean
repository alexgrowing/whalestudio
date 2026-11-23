import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

namespace GlobalTheory.HilbertThetaSeries.GaussSumCharacter

section General

variable {M : Type} [AddCommGroup M] {q : M → ℂ} {β : M → M → ℂ} {e : ℕ}

end General

section Four

variable {M : Type} [AddCommGroup M]

def uI (x : Fin 4 → M) : Fin 4 → M := ![-x 1, x 0, -x 3, x 2]

def uJ (x : Fin 4 → M) : Fin 4 → M := ![-x 2, x 3, x 0, -x 1]

def uK (x : Fin 4 → M) : Fin 4 → M := ![-x 3, -x 2, x 1, x 0]

def quat (a b c d : ℤ) : (Fin 4 → M) →+ (Fin 4 → M) :=
  AddMonoidHom.mk' (fun x => a • x + b • uI x + c • uJ x + d • uK x) (by
    intro x y
    ext i
    fin_cases i <;> simp [uI, uJ, uK] <;> module)

end Four

end GlobalTheory.HilbertThetaSeries.GaussSumCharacter

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
