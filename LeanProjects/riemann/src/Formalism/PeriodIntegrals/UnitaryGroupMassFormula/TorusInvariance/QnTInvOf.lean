import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.TransferInvarianceCongruence

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.FourierDecayAlt.Q

theorem qnTInv_of (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH) :
    TInvariant :=
  tInvariant_of_contractions hCC hP hG hL transfer_invariance_smooth transfer_invariance_group_mul transfer_invariance_vector transfer_invariance_congruence
    transfer_invariance_right transfer_invariance_restriction

end Formalism.FourierDecayAlt.Q.TInvW
