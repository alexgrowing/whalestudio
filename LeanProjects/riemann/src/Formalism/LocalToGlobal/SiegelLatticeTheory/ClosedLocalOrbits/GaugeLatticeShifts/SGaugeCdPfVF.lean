import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeCdPfV
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MpUncurry

noncomputable section

namespace Formalism.MainNotions.S.Gauge

theorem lamVol_of_sum_equiv {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : LamVol ε e :=
  CdV.lamVol_of ε e (mp_cF ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q)))

end Formalism.MainNotions.S.Gauge
