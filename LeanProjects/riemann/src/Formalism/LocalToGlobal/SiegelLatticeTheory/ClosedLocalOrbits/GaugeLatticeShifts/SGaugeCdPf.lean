import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfM
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfVF

namespace Formalism.MainNotions.S.Gauge

theorem complex_gauge_normalization (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D) (n : ℕ) (ε : Fin n → Bool) : CdGauge D n ε :=
  cdGauge_of_lamVol D hcd (fun ε e => lamVol_of_sum_equiv ε e) n ε

end Formalism.MainNotions.S.Gauge
