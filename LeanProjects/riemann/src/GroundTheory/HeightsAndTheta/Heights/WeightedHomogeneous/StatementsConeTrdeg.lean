import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

def ConeTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), Geo.Birational y → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Geo.IsHorizontal (Geo.mCoordIdeal y) →
        Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ Ω + Fintype.card K

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights
