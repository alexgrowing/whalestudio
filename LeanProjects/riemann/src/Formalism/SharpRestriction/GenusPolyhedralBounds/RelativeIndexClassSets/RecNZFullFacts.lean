import Mathlib

namespace Formalism.MainNotions.Gaps.RN

def LenBaseChangeDVR : Prop :=
  ∀ (A O : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (f : A →+* O), IsLocalHom f → Function.Injective f →
    ∀ (ϖ : A), Irreducible ϖ → ∀ (ι : Type) [Fintype ι] (N : Submodule A (ι → A)),
      Module.length O ((ι → O) ⧸ Submodule.span O ((fun x : ι → A => f ∘ x) '' (N : Set (ι → A)))) =
        ((IsDiscreteValuationRing.addVal O (f ϖ)).toNat : ℕ∞) * Module.length A ((ι → A) ⧸ N)

end Formalism.MainNotions.Gaps.RN
