import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeRA

noncomputable section

namespace Formalism.L2.SG.Pf

theorem iotaDictAllC_holds : IotaDictAllC := iotaDictAllC_of iotaBridgeRAC_holds

theorem iotaDictC_holds : IotaDictC := iotaDictC_holds_of iotaBridgeRAC_holds

end Formalism.L2.SG.Pf
