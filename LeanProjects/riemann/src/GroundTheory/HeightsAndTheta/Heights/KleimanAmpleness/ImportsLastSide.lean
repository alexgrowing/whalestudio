import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def ZeroIdealEq.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ) (Ω : Type) [Field Ω] [Algebra S Ω] (x : Fin (N + 1) → Ω)
    (D : Kleiman.LineBundle S x) (n : ℤ) (m : ℕ) (s : Fin m → Ω), (∃ i, x i ≠ 0) → IsGraphGen D n s →
    ∀ σ : Ω, Kleiman.zeroIdeal D.toSubSystem σ =
      (IndefiniteRowSideFullHecke.Kleiman2.divIdeal S (graphVec x s) (graphDeg n) σ).comap
        (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ k, graphIdx N m k))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
