import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

namespace Formalism.MainNotions.StandardLattice

theorem nonvanishing_bessel_period (D : Formalism.BasicNotions.D7) : NonvanishingBesselPeriod D :=
  fun _ _ lam _ _ _ _ _ σ h => Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ h

end Formalism.MainNotions.StandardLattice
