import Mathlib
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem spec_local_hom_factors_affineOpen : ∀ (X : Scheme.{0}) (V : X.Opens) (hV : IsAffineOpen V)
    (A : Type) [CommRing A] [IsLocalRing A]
    (f : Spec (CommRingCat.of A) ⟶ X), f (IsLocalRing.closedPoint A) ∈ V →
    ∃ g : Γ(X, V) →+* A, f = Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec := by
  intro X V hV A _ _ f hf
  have H : Set.range f ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have hs : x ⤳ IsLocalRing.closedPoint A := IsLocalRing.specializes_closedPoint x
    exact (hs.map f.continuous).mem_open V.isOpen hf
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec f H)).hom, ?_⟩
  simp [IsOpenImmersion.lift_fac]

end GlobalTheory
