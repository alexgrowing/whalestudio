import Mathlib

universe u_1

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.SchemeDominantSpecMap

theorem appTop_injective {R A : CommRingCat.{u_1}} (φ : R ⟶ A) (h : Function.Injective φ) :
    Function.Injective (Spec.map φ).appTop := by

  have e : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality φ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1.comp
    (h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1)

theorem isSchemeTheoreticallyDominant_specMap {R A : CommRingCat.{u_1}} (φ : R ⟶ A)
    (h : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot (Spec.map φ).appTop.hom).1 (appTop_injective φ h),
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]

end GlobalTheory.SchemeDominantSpecMap
