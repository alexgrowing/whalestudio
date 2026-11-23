import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BruhatHaarOfSandwich
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsGaugeNormalizedStabilizer

noncomputable section

namespace Formalism.L2.SG.Pf

theorem jacGauge_of_sandwich_rhsWLim (hS : BH.Sandwich) (hL : WB.RhsWLim) : JacGauge :=
  jacGauge_of_hearts3 hS GE.existsGaugeNormalizedStabilizer hL

end Formalism.L2.SG.Pf
