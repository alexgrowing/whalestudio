import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinJumpSumLeOfPowMemOfInertiaEqTopStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_pow_growth :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B C : Subgroup (L ≃ₐ[K] L)), A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ ∈ A, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild K L) A B) (jumpSum (wild K L) A B + E) ≤ jumpSum (wild K L) A C := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B C hA hE hC hB
  obtain ⟨j, hj, hr, -, hG⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A
  have hmem : ∀ σ, j σ ∈ A := fun σ => hr.le ⟨σ, rfl⟩
  have hw : wild ↥(IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hG _
  have h0 : lowerRamificationGroup ↥(IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hG, eq_top_iff]
    intro σ _
    exact hA (hmem σ)
  have key := GlobalTheory.T.min_jumpSum_le_jumpSum_of_totally_ramified ↥(IntermediateField.fixedField A) L p E (B.comap j) (C.comap j) h0 hE
    (fun σ τ => by
      have := hC _ (hmem σ) _ (hmem τ)
      simpa [Subgroup.mem_comap, map_mul, map_inv] using this)
    (fun σ h => by
      have h' : j σ ^ p ∈ C := by simpa [Subgroup.mem_comap, map_pow] using h
      exact hB _ (hmem σ) h')
  rw [hw, jumpSum_comap_injective _ _ j _ B hj, jumpSum_comap_injective _ _ j _ C hj, hr] at key
  exact key

end GlobalTheory.PMon.Ram
