import Mathlib
import GroundTheory.LocalFields.ArtinConductorInduced
import GroundTheory.LocalFields.BrauerInductionInduced

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Module Representation

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Linear

variable (K L) in

theorem charArtinConductor_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (χ : ι → (L ≃ₐ[K] L) → ℂ) :
    charArtinConductor K L (∑ i ∈ s, c i • χ i) = ∑ i ∈ s, c i * charArtinConductor K L (χ i) := by
  simp only [charArtinConductor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun σ _ ↦ by ring

end Linear

section ConductorDiscriminant

variable [IsGalois K L]

theorem sum_irrChars_mul_charArtinConductor :
    ∑ χ ∈ irrChars (L ≃ₐ[K] L), χ 1 * charArtinConductor K L χ =
      ((residueDegree K L * differentExponent K L : ℕ) : ℂ) := by
  classical
  rw [← charArtinConductor_regular, ← charArtinConductor_sum]
  congr 1
  rw [← character_leftRegular_eq_sum]
  funext σ
  rw [character_leftRegular_apply, Nat.card_eq_fintype_card]

theorem addVal_discr_eq_sum_irrChars {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] 𝒪[L]) :
    ∃ n : ℕ, IsDiscreteValuationRing.addVal 𝒪[K] (Algebra.discr 𝒪[K] b) = n ∧
      (n : ℂ) = ∑ χ ∈ irrChars (L ≃ₐ[K] L), χ 1 * charArtinConductor K L χ := by
  refine ⟨_, addVal_discr_eq_artinCharacter_one b, ?_⟩
  rw [sum_irrChars_mul_charArtinConductor, artinCharacter_one, Int.toNat_natCast]

end ConductorDiscriminant

section Induced

variable (M : IntermediateField K L)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] in

theorem inducedFun_eq_indFun (ψ : (L ≃ₐ[M] L) → ℂ) :
    inducedFun ψ = indFun (AlgEquiv.restrictScalarsHom K) ψ := by
  funext s
  rfl

variable [IsGalois K L]

end Induced

end GroundTheory.LocalField
