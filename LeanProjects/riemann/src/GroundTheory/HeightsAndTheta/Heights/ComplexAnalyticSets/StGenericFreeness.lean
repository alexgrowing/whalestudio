import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

def GenericFreeness.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] [Module.Finite B M],
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

end GroundTheory.Heights₂.Heights
