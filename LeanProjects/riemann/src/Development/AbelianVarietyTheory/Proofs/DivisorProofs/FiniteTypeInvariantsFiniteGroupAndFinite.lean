import Mathlib

namespace GlobalTheory

theorem finiteType_invariants_and_finite (R : Type) [CommRing R] [IsNoetherianRing R]
    (C' : Type) [CommRing C'] [Algebra R C'] [Algebra.FiniteType R C']
    (G : Type) [Group G] [Finite G] (act : G →* (C' ≃ₐ[R] C')) (C : Subalgebra R C')
    (hC : ∀ x, x ∈ C ↔ ∀ σ, act σ x = x) :
    Algebra.FiniteType R C ∧ Module.Finite C C' := by
  letI : MulSemiringAction G C' := MulSemiringAction.compHom C' act
  haveI : Algebra.IsInvariant C C' G := ⟨fun b hb => ⟨⟨b, (hC b).2 fun σ => hb σ⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral C C' := Algebra.IsInvariant.isIntegral C C' G
  haveI : Algebra.FiniteType C C' := Algebra.FiniteType.of_restrictScalars_finiteType R C C'
  haveI hfin : Module.Finite C C' := Algebra.IsIntegral.finite
  refine ⟨⟨fg_of_fg_of_fg (A := R) (B := C) (C := C') Algebra.FiniteType.out
    hfin.fg_top Subtype.val_injective⟩, hfin⟩

end GlobalTheory
