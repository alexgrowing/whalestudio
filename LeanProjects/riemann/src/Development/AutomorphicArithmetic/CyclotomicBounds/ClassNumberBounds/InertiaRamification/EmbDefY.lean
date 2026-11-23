import Mathlib

namespace KStar.Ram

open IsLocalRing NumberField

def embOver {B : Type*} [CommRing B] (R : Type*) [CommRing R] [IsLocalRing R] (P : Ideal B) :
    Set (B →+* R) :=
  {σ | (maximalIdeal R).comap σ = P}

def inertiaCoset {B R : Type*} [CommRing B] [CommRing R] [IsLocalRing R] (τ : B →+* R) :
    Set (B →+* R) :=
  {σ | ∀ x, σ x - τ x ∈ maximalIdeal R}

end KStar.Ram
