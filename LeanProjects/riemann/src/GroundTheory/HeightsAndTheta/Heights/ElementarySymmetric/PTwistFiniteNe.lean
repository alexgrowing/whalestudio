import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistPowZeroSub
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

theorem TwistFiniteNe.proof (hT1 : Kleiman.TwistFinite.Statement.{0, 0}) : TwistFiniteNe.Statement :=
  (TwistFinite.equiv_ne LineBundle.proof).mp hT1

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
