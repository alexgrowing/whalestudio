import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef

namespace DiscreteGroups.sglob.DzType

theorem sixteen_sq_lt_g (D : Formalism.BasicNotions.D7) (k : Fin 2) : 16 * D.R.r ^ 2 < D.host.g k :=
  big_of_le_nV D k (by unfold Formalism.BasicNotions.Ranks.nV; omega)

end DiscreteGroups.sglob.DzType
