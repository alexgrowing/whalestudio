import Mathlib

namespace PI

open Matrix

def SmithDiag.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) R),
    ∃ (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      IsUnit U ∧ IsUnit V ∧ U * A * V = diagonal d

def SmithMat.{u} : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) R),
    ∃ (U V : Matrix (Fin n) (Fin n) R) (d : Fin n → R),
      IsUnit U ∧ IsUnit V ∧ U * A * V = diagonal d ∧ ∀ i j, i ≤ j → d i ∣ d j

end PI
