import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottComplex.StSpecOf

universe u

namespace PIW.ENSpec

open PI.EagonNorthcott MvPolynomial RingTheory.Sequence

section Nat

variable {R : Type u} [CommRing R] {D : ℕ} (x : Fin D → R)

lemma ev_lin (c : Fin D → ℤ) : eval x (lin (X : Fin D → MvPolynomial (Fin D) R) c) = lin x c := by
  simp [lin]

end Nat

end PIW.ENSpec
