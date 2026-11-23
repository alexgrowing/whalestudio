import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

namespace Formalism.L2.SG.Pf

theorem massAC_holds : Formalism.L2.SG.NormCut.MassAC :=
  massAC_of Formalism.L2.SG.Closed.NeatC_holds

end Formalism.L2.SG.Pf
