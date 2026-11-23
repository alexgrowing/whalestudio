import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def AmpleEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω),
    IsGraphGen Q n s → Nonempty (Kleiman.AmpleData S x Q) →
      IndefiniteRowSideFullHecke.Kleiman2.IsAmpleByFiniteMap S (graphVec x s) (graphDeg n)

def AmpleConverseFalse.Statement : Prop :=
  ∀ (k : Type) [Field k],
    IndefiniteRowSideFullHecke.Kleiman2.IsAmpleByFiniteMap k (graphVec (Kleiman.lineX k) (fun _ : Fin 1 => (1 : RatFunc k)))
                              (graphDeg 0) ∧
      IsEmpty (Kleiman.AmpleData k (Kleiman.lineX k) (Kleiman.twistBundle k (Kleiman.lineX k) 0))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
