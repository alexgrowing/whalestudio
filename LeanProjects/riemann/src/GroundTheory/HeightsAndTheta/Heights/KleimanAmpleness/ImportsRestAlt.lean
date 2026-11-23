import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def NumEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (pp : Ideal (Kleiman.Poly k N)) (e : ℕ) (b : Fin e → ℤ),
    Kleiman.IsSubvar x pp e →
    Kleiman.interNum pp (fun i => Kleiman.twistSys k x (b i)) =
      NumbersDVR.intNum k (pp.comap (Kleiman.oneBlock (S := k) (N := N))) (fun i (_ : Unit) => b i)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
