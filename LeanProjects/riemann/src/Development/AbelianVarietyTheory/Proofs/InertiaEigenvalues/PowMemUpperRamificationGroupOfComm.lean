import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.ConductorTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupRealStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_of_comm : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e v hcomm hv hord σ hσ

  let f : M →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let φ : M ≃ₐ[F] f.fieldRange := f.equivFieldRange
  haveI : FiniteDimensional F f.fieldRange := LinearEquiv.finiteDimensional φ.toLinearEquiv
  haveI : IsMulCommutative (M ≃ₐ[F] M) := ⟨⟨hcomm⟩⟩
  haveI : IsAbelianGalois F M := IsAbelianGalois.mk
  haveI : IsAbelianGalois F f.fieldRange := IsAbelianGalois.of_algHom φ.symm.toAlgHom

  have h1 : φ.autCongr σ ∈ upperRamificationGroup F f.fieldRange v := by
    rw [← map_upperRamificationGroup_autCongr φ v]
    exact ⟨σ, hσ, rfl⟩
  have h2 := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_real F f.fieldRange p e v hv hord _ h1
  rw [← map_upperRamificationGroup_autCongr φ] at h2
  obtain ⟨τ, hτ, hτσ⟩ := h2
  have hτ' : τ = σ ^ p := φ.autCongr.injective (by simpa [map_pow] using hτσ)
  exact hτ' ▸ hτ

end GlobalTheory.PMon.Ram
