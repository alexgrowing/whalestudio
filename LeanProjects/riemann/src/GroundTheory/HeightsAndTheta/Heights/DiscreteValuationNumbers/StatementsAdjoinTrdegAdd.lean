import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def AdjoinTrdegAdd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (L : Type) [CommRing L] [IsDomain L] [Algebra R L],
    Function.Injective (algebraMap R L) →
    ∀ (s t : Set L) (ι : Type) [Fintype ι] (x : ι → L), Set.range x ⊆ t →
      AlgebraicIndependent (Algebra.adjoin R s) x →
      (∀ a ∈ t, IsAlgebraic (Algebra.adjoin R (s ∪ Set.range x)) a) →
      Algebra.trdeg R (Algebra.adjoin R (s ∪ t)) =
        Algebra.trdeg R (Algebra.adjoin R s) + (Fintype.card ι : Cardinal)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
