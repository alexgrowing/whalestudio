import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem baseChange_fixedField :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (A : Subgroup (L ≃ₐ[K] L)), ∃ j : (L ≃ₐ[↥(IntermediateField.fixedField A)] L) →* (L ≃ₐ[K] L), Function.Injective j ∧ j.range = A ∧ (∀ σ x, j σ x = σ x) ∧ ∀ i : ℤ, lowerRamificationGroup ↥(IntermediateField.fixedField A) L i = (lowerRamificationGroup K L i).comap j := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ A
  refine ⟨AlgEquiv.restrictScalarsHom K, AlgEquiv.restrictScalarsHom_injective K, ?_, ?_, ?_⟩
  · rw [GroundTheory.LocalField.range_restrictScalarsHom, IntermediateField.fixingSubgroup_fixedField]
  · intro σ x
    rfl
  · intro i
    exact (lowerRamificationGroup_comap_restrictScalars (IntermediateField.fixedField A) i).symm

end GlobalTheory.PMon.Ram
