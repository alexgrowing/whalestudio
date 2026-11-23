import Mathlib

universe u

namespace PI

def RegSeqQuasiReg : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (x : Fin n → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) →
    ∀ (k : ℕ) (F : MvPolynomial (Fin n) R), F.IsHomogeneous k →
      MvPolynomial.eval x F ∈ Ideal.span (Set.range x) ^ (k + 1) →
      ∀ m, F.coeff m ∈ Ideal.span (Set.range x)

end PI
