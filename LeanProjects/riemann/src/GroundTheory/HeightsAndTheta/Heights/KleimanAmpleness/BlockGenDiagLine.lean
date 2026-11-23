import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

def BlockGen (S : Type*) [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) : Prop :=
  ∀ j : ι k₀, y ⟨k₀, j⟩ ≠ 0 → ∀ k, ∃ w : ι k → Ω,
    (∀ a b, y ⟨k, a⟩ * w b ∈
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j)) ∧
      ∑ b, y ⟨k, b⟩ * w b = 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
