import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ChartKernel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (Ω : Type) [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (Ω' : Type) [Field Ω'] [Algebra S Ω'] (y' : (Σ k, ι k) → Ω'),
    mIdealOver S y ≤ mIdealOver S y' → ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∀ g : MvPolynomial (Σ k, ι k) S, aeval (fun p => y p / y ⟨p.1, c p.1⟩) g = 0 →
        aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
