import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def Ample.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (H : Kleiman.LineBundle S x), Kleiman.AmpleData S x H →
    Nonempty (IndefiniteRowSideFullHecke.Kleiman.AmpleData S x (toIndefiniteRowSideFullHecke H.toSubSystem))

noncomputable def Ample.hyps (k : Type) [Field k] :
    Kleiman.AmpleData k (Kleiman.lineX k) (Kleiman.twistBundle k (Kleiman.lineX k) 1) :=
  Kleiman.twistAmple k (Kleiman.lineX k)

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
