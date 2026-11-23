import Mathlib
import Formalism.PeriodIntegrals.KoszulExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.Ii
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KoszulExactness.KoszulImageInIdeal

universe u

namespace PI.KEX

open PI.KoszulExact

section Lemmas

variable {R : Type u} [CommRing R] {D : ℕ}

theorem form_single (s : Fin D → R) (k : Fin D) : form s (Pi.single k 1) = s k := by
  simp [form, Pi.single_apply]

end Lemmas

end PI.KEX
