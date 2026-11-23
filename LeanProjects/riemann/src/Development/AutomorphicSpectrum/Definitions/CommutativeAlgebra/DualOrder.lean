import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

def pullFun (R : Type) [CommRing R] (ι : H →* T) : (T → R) →ₐ[R] (H → R) :=
  Pi.algHom R _ fun h => Pi.evalAlgHom R (fun _ : T => R) (ι h)

def resOrder (ι : H →* T) (A : Subalgebra R (T → R)) : Subalgebra R (H → R) := A.map (pullFun R ι)

def quotOrder (π : T →* H) (A : Subalgebra R (T → R)) : Subalgebra R (H → R) := A.comap (pullFun R π)

def muOrder (R : Type) [CommRing R] (T : Type) [CommGroup T] : Subalgebra R (T → R) :=
  Algebra.adjoin R {f | ∃ χ : T →* Rˣ, f = fun t => ((χ t : Rˣ) : R)}

def dualOrder (A : Subalgebra R (T → R)) : Subalgebra R ((T →* Rˣ) → R) :=
  Algebra.adjoin R {g | ∃ l : A →ₗ[R] R, ∀ (χ : T →* Rˣ) (h : (fun t => ((χ t : Rˣ) : R)) ∈ A), g χ = l ⟨_, h⟩}

end GlobalTheory.CompanionTheory.Ar.BT
