import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.EqZeroOrIsHomogeneousOfMemPolyPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def LineBundle.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω),
    (∀ Q : Kleiman.LineBundle S x,
      ∃ Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x, ∀ i, Q'.mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i) ∧
    ∀ Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x,
      ∃ Q : Kleiman.LineBundle S x, ∀ i, x i ≠ 0 → Q'.mods i = toIndefiniteRowSideFullHecke Q.toSubSystem i

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
