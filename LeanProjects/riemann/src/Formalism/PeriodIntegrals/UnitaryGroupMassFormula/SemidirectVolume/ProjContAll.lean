import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjCont
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

theorem representation_continuous : PiCont := by
  intro F E _ _ _ _ _ σ M J r P T hσσ hJ hP
  have := (Lc.tensor_adele_topology_holds F E).1
  exact continuous_piG hσσ hJ hP

end PI.VolSemiDirect.W
