import Mathlib

noncomputable section

namespace GlobalTheory.DblUnip

open Matrix

variable {R : Type} [CommRing R] {d : ℕ}

def unipMat (c : R →+* R) (J : Matrix (Fin d) (Fin d) R) (x₀ y₀ : Fin d → R) (β : R) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R :=
  fromBlocks 1 (β • vecMulVec x₀ (J *ᵥ fun i => c (y₀ i))) (-(c β) • vecMulVec y₀ (J *ᵥ fun i => c (x₀ i))) 1

def diagMat (c : R →+* R) (J : Matrix (Fin d) (Fin d) R) (x₀ y₀ : Fin d → R) (β : R) : Matrix (Fin d) (Fin d) R :=
  1 - c β • vecMulVec y₀ (J *ᵥ fun i => c (x₀ i))

end GlobalTheory.DblUnip

end
