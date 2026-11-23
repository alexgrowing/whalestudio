import Formalism.PeriodIntegrals.EagonNorthcott

noncomputable section

namespace PI

open EagonNorthcott in

def EagonNorthcottSpec.{u} : Prop :=
  ∀ (D a : ℕ) (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) a e C →
      ∀ (R : Type u) [CommRing R] (x : Fin D → R),
        RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) → Resolves x a e C

end PI
