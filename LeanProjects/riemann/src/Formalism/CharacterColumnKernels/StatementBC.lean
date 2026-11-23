import Formalism.CharacterColumnKernels.StatementN

open Finset

noncomputable section

namespace Formalism.NG

def StatVccBaseChange : Prop :=
  ∀ (O O' : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [Module.Free O O']
    [Module.Finite O O'] (e : ℕ),
    (∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y) →
    ∀ (X : Type*) (T : Subalgebra O (X → O)) (T' : Subalgebra O' (X → O')),
      (T' : Set (X → O')) = Submodule.span O' ((fun f : X → O => algebraMap O O' ∘ f) '' (T : Set (X → O))) →
    ∀ (Z : Set X) (x : X), vcc T' Z x = e * vcc T Z x

end Formalism.NG
