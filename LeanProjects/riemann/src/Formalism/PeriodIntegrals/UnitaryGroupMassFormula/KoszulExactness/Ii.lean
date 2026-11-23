import Mathlib
import Formalism.PeriodIntegrals.KoszulExact

noncomputable section

universe u

namespace PI.KoszulExact

def eb (R : Type u) [CommRing R] {D : ℕ} (k : Fin D) : ExteriorAlgebra R (Fin D → R) :=
  ExteriorAlgebra.ι R (Pi.single k 1)

def Li (R : Type u) [CommRing R] (D : ℕ) (i : ℕ) : Submodule R (ExteriorAlgebra R (Fin D → R)) :=
  Submodule.span R (eb R '' {k : Fin D | (k : ℕ) < i})

def Ii {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) : Ideal R :=
  Ideal.span (s '' {k : Fin D | (k : ℕ) < i})

end PI.KoszulExact
