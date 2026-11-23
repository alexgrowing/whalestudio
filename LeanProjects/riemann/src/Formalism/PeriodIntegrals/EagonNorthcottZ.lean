import Formalism.PeriodIntegrals.EagonNorthcott

noncomputable section

namespace PI

open EagonNorthcott in

def EagonNorthcottZ : Prop :=
  ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Shape D a n e C ∧ Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) a e C

end PI
