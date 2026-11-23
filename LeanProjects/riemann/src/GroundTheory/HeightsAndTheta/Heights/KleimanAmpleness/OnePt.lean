import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

noncomputable def onePt (k : Type) [Field k] : Fin (0 + 1) → RatFunc k := fun _ => 1

def GenericHypGap.Statement : Prop :=
  ∀ (k : Type) [Field k],
    Kleiman.IsDomination k (onePt k) (Kleiman.lineX k) ∧
    (∀ (i : Fin (0 + 1)) (hi : onePt k i ≠ 0), ∀ b ∈ Kleiman.domRing k (onePt k) (Kleiman.lineX k) i,
      ∃ s : k, algebraMap k (RatFunc k) s ≠ 0 ∧
        algebraMap k (RatFunc k) s * b ∈ Kleiman.chartRing k (onePt k) (Kleiman.singleChart hi)) ∧
    ¬ IndefiniteRowSideFullHecke.Kleiman2.SameModel k (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (Kleiman.lineX k)) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (onePt k))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
