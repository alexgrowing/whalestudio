import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def NefGenericLocalize.Statement : Prop :=
  NefGenericDVR.Statement → Kleiman.NefGeneric.Statement.{0, 0}

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
