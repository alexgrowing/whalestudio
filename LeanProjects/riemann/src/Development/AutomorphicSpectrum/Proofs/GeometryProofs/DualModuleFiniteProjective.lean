import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo.HomDual

noncomputable def homEquivDual (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] :
    (P →ₗ[R] Localization.Away f) ≃ₗ[Localization.Away f] Module.Dual (Localization.Away f) P :=
  { toFun := fun g =>
      LinearMap.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f) g
    invFun := fun g => g.restrictScalars R
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem finite_projective_hom : ∀ (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
    [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P]
    [Module.Finite (Localization.Away f) P] [Module.Projective (Localization.Away f) P],
    Module.Finite (Localization.Away f) (P →ₗ[R] Localization.Away f) ∧
      Module.Projective (Localization.Away f) (P →ₗ[R] Localization.Away f) := by
  intro R P _ f _ _ _ _ _ _
  let e := homEquivDual R P f
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

end GlobalTheory.CompanionTheory.Ggeo.HomDual
