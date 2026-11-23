import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial

variable {D : ℕ}

abbrev Cnd (ι : Fin D → Fin D ⊕ Fin D) (i : Fin D) (m : (Fin D ⊕ Fin D) →₀ ℕ) : Prop :=
  0 < m (ι i) ∧ ∀ l, l < i → m (ι l) = 0

end PI.EagonNorthcottZ
