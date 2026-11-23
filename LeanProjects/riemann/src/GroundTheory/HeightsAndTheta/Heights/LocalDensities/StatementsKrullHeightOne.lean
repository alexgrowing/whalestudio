import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

def KrullHeightOne.Hyp {A : Type*} [CommRing A] (p q : A) : Prop :=
  q ≠ 0 ∧ ¬ q ∣ p

def KrullHeightOne.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (p q : A),
    KrullHeightOne.Hyp p q →
      ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧ ∃ c ∉ P, ∃ t ∈ P, c * q = t * p

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
