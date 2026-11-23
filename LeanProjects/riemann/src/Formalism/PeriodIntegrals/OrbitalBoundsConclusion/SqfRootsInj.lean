import Mathlib
import Formalism.PeriodIntegrals.SqfRootsInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.WitMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.RpowQuarterPowFour

theorem squarefree_roots_injective : PI.SqfRootsInj.Claim :=
  PI.SqfRootsInj.W.claim_of PI.SqfRootsInj.W.counted_labels_have_witness PI.SqfRootsInj.W.local_orbit_count
