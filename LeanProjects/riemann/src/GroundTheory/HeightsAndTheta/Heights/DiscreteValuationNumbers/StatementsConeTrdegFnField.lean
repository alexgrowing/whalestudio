import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal fnField)

def ConeTrdegFnField.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (Ω : Type) [Field Ω] [Algebra O Ω],
    Function.Injective (algebraMap O Ω) →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
      (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Algebra.trdeg O (MRingOver O ι ⧸ mcIdeal O y) =
        Algebra.trdeg O (Algebra.adjoin O (fnField O y : Set Ω)) + Fintype.card K

end GroundTheory.Heights₂.Heights.NumbersDVR
