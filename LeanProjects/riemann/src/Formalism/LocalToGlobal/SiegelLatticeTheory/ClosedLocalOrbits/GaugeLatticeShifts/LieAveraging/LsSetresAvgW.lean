import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.AvgCore

namespace Formalism.L2.SG.TermOp.Vanish

theorem avgCore : AvgCore :=
  fun G _ _ _ _ _ _ _ _ μ _ _ R Γ V _ _ χ f Ω hR hΓR hdisc hcpt _ hχm hχΓ hχne hf hΩ =>
    Formalism.L2.SG.AvgPf.avg_core G μ R Γ V χ f Ω hR hΓR hdisc hcpt hχm hχΓ hχne hf hΩ

end Formalism.L2.SG.TermOp.Vanish
