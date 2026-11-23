import Development.EtaleCohomology.EtaleTrace.GenEtalePf

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem etaleOverBasic : EtaleOverBasic := by
  intro X P π U hU hU' a H
  have hle : π ⁻¹ᵁ P.basicOpen a ≤ π ⁻¹ᵁ U := π.preimage_mono (P.basicOpen_le a)
  have key : RingHom.Etale (π.app (P.basicOpen a)).hom := by
    letI := (π.app U).hom.toAlgebra
    letI : Algebra Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    letI : Algebra Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app _).hom.toAlgebra
    letI : Algebra Γ(P, U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) Γ(X, π ⁻¹ᵁ P.basicOpen a) := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Γ(P, U) Γ(P, P.basicOpen a) Γ(X, π ⁻¹ᵁ P.basicOpen a) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      show (π.app U ≫ X.presheaf.map (homOfLE hle).op).hom =
        (P.presheaf.map (homOfLE (P.basicOpen_le a)).op ≫ π.app (P.basicOpen a)).hom
      rw [π.naturality]; rfl
    have hA : IsLocalization.Away a Γ(P, P.basicOpen a) := hU.isLocalization_basicOpen a
    have gen : ∀ (W : X.Opens) (e : W ≤ π ⁻¹ᵁ U), W = X.basicOpen (π.app U a) →
        @IsLocalization.Away _ _ (π.app U a) Γ(X, W) _ (X.presheaf.map (homOfLE e).op).hom.toAlgebra := by
      rintro W e rfl; exact hU'.isLocalization_basicOpen _
    exact H _ _ hA (gen _ hle (π.preimage_basicOpen a))
  haveI : IsAffine (P.basicOpen a).toScheme := hU.basicOpen a
  haveI : IsAffine (π ⁻¹ᵁ P.basicOpen a).toScheme := by
    have := hU'.basicOpen (π.app U a); rw [← π.preimage_basicOpen a] at this; exact this
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
  have hW : (P.basicOpen a).ι ''ᵁ ⊤ = P.basicOpen a := by simp
  have gen2 : ∀ (W : P.Opens) (T : X.Opens) (h : T = π ⁻¹ᵁ W), W = P.basicOpen a →
      RingHom.Etale (π.app W ≫ X.presheaf.map (eqToHom h).op).hom := by
    rintro W T h rfl
    subst h
    simpa using key
  exact gen2 _ _ _ hW

end LateralTheory.EtaleTrace.Cov
