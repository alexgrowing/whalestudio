import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurIrreducible

namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

theorem schurStep : SchurStep :=
  _root_.UpperTheory.Reformulated.B.SchurIrreducible.schurStep

end PI.UnitaryGroupMassFormula.CommMult
