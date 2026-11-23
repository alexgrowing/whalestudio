import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfA
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfL
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfT

namespace Formalism.MainNotions.S.Gauge

theorem cdGauge_of_lamVol (D : Formalism.BasicNotions.D7) (hcd : Formalism.BasicNotions.cdScaleTie D)
    (hL : ∀ {m P Q : ℕ} (ε : Fin m → Bool) (e : Fin P ⊕ Fin Q ≃ Fin m), LamVol ε e)
    (n : ℕ) (ε : Fin n → Bool) : CdGauge D n ε :=
  cdGauge_of_parts D hcd (fun ε => l1BallDensity_signs ε) (fun ε => l1BallMeasurable_signs ε) hL (fun ε e => setEq ε e) (fun ε e => upqIn ε e) n ε

end Formalism.MainNotions.S.Gauge
