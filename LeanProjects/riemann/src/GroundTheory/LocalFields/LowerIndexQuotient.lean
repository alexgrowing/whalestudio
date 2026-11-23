import Mathlib
import GroundTheory.LocalFields.LowerIndex
import GroundTheory.LocalFields.IntermediateField
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RamificationLowerIndex
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactAlt

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial

theorem addVal_prod {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ι : Type*}
    (s : Finset ι) (f : ι → R) : addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) :=
  _root_.Bl.general_b_fact'''''''.goal1 s f

section Restrict

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L)

theorem restrictNormalHom_restrictScalars [Normal K M] (τ : L ≃ₐ[M] L) :
    AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M]
  exact ⟨τ, rfl⟩

theorem exists_eq_mul_restrictScalars_of_restrictNormalHom_eq [Normal K M] {σ ρ : L ≃ₐ[K] L}
    (h : AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ) :
    ∃ τ : L ≃ₐ[M] L, σ * τ.restrictScalars K = ρ := by
  have hker : σ⁻¹ * ρ ∈ (AlgEquiv.restrictNormalHom M).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M] at hker
  obtain ⟨τ, hτ⟩ := hker
  refine ⟨τ, ?_⟩
  rw [← AlgEquiv.restrictScalarsHom_apply, hτ, mul_inv_cancel_left]

end Restrict

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section

variable (M : IntermediateField K L)

theorem integerAlgEquiv_restrictScalars_algebraMap (τ : L ≃ₐ[M] L) (y : 𝒪[M]) :
    integerAlgEquiv K L (τ.restrictScalars K) (algebraMap 𝒪[M] 𝒪[L] y) = algebraMap 𝒪[M] 𝒪[L] y := by
  apply Subtype.ext
  rw [coe_integerAlgEquiv_apply, coe_algebraMap_integer, AlgEquiv.restrictScalars_apply]
  exact τ.commutes _

variable [IsGalois K L]

theorem ramificationIndex_mul_lowerIndex_restrictNormalHom [Normal K M] (σ : L ≃ₐ[K] L) :
    (ramificationIndex M L : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
      ∑ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) :=
  by apply _root_.UpperTheory.Reformulated.B.RamificationLowerIndex.ramificationIndex_mul_lowerIndex_restrictNormalHom <;> assumption

open Classical in

theorem ramificationIndex_mul_lowerIndex_eq_sum_fiber [Normal K M] (s : M ≃ₐ[K] M) :
    (ramificationIndex M L : ℕ∞) * lowerIndex K M s =
      ∑ σ ∈ Finset.univ.filter (fun σ : L ≃ₐ[K] L ↦ AlgEquiv.restrictNormalHom M σ = s),
        lowerIndex K L σ := by
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L s
  rw [ramificationIndex_mul_lowerIndex_restrictNormalHom]
  refine Finset.sum_bij (fun τ _ ↦ σ * τ.restrictScalars K) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro τ _
    rw [Finset.mem_filter, map_mul, restrictNormalHom_restrictScalars, mul_one]
    exact ⟨Finset.mem_univ _, rfl⟩
  · intro a _ b _ hab
    exact AlgEquiv.restrictScalars_injective K (mul_left_cancel hab)
  · intro ρ hρ
    obtain ⟨τ, hτ⟩ := exists_eq_mul_restrictScalars_of_restrictNormalHom_eq M
      (Finset.mem_filter.mp hρ).2
    exact ⟨τ, Finset.mem_univ _, hτ⟩

omit [IsGalois K L] in

theorem exists_lowerIndex_mul_eq_min (σ : L ≃ₐ[K] L) :
    ∃ τ₀ : L ≃ₐ[M] L,
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤
        lowerIndex K L (σ * τ₀.restrictScalars K)) ∧
      ∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ₀.restrictScalars K * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L (σ * τ₀.restrictScalars K)) := by
  obtain ⟨τ₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun τ : L ≃ₐ[M] L ↦ lowerIndex K L (σ * τ.restrictScalars K)) Finset.univ_nonempty
  refine ⟨τ₀, fun τ ↦ hmax τ (Finset.mem_univ _), fun τ ↦ ?_⟩
  set σ₀ := σ * τ₀.restrictScalars K with hσ₀
  rw [← lowerIndex_restrictScalars (K := K)]
  rcases lt_or_ge (lowerIndex K L (τ.restrictScalars K)) (lowerIndex K L σ₀) with h | h
  · rw [lowerIndex_mul_of_lt h, min_eq_left h.le]
  · rw [min_eq_right h]
    refine le_antisymm ?_ ((min_eq_left h).symm.le.trans (min_le_lowerIndex_mul _ _))
    have hm : (τ₀ * τ).restrictScalars K = τ₀.restrictScalars K * τ.restrictScalars K :=
      AlgEquiv.ext fun _ ↦ rfl
    have := hmax (τ₀ * τ) (Finset.mem_univ _)
    rwa [hm, ← mul_assoc] at this

theorem exists_ramificationIndex_mul_lowerIndex_eq_sum_min [Normal K M] (σ : L ≃ₐ[K] L) :
    ∃ σ₀ : L ≃ₐ[K] L, AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤ lowerIndex K L σ₀) ∧
      (ramificationIndex M L : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
        ∑ τ : L ≃ₐ[M] L, min (lowerIndex M L τ) (lowerIndex K L σ₀) := by
  obtain ⟨τ₀, hmax, hmin⟩ := exists_lowerIndex_mul_eq_min M σ
  have hres : AlgEquiv.restrictNormalHom M (σ * τ₀.restrictScalars K) =
      AlgEquiv.restrictNormalHom M σ := by
    rw [map_mul, restrictNormalHom_restrictScalars, mul_one]
  refine ⟨σ * τ₀.restrictScalars K, hres, hmax, ?_⟩
  rw [← hres, ramificationIndex_mul_lowerIndex_restrictNormalHom]
  exact Finset.sum_congr rfl fun τ _ ↦ hmin τ

end

end GroundTheory.LocalField
