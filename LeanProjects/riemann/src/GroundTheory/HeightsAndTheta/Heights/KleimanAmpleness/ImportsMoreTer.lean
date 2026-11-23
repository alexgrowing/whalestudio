import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def DomEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N N' : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (x' : Fin (N' + 1) → Ω),
    (Kleiman.IsDomination S x x' ↔
      IndefiniteRowSideFullHecke.Kleiman2.Dominates S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) ∧
    (Kleiman.IsDomination S x x' → ∀ (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
      IsGraphGen Q n s →
        Kleiman.pullSecs x' Q.toSubSystem =
          secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (graphVec x s))
            (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (graphDeg n)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
