import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Uniqueness
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.UnitsBasic
import GroundTheory.LocalFields.UnitsPowers

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Action

variable {K L}

theorem integerAlgEquiv_mem_maximalIdeal_pow_iff (σ : L ≃ₐ[K] L) (n : ℕ) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x ∈ 𝓂[L] ^ n ↔ x ∈ 𝓂[L] ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hσϖ : Irreducible (integerAlgEquiv K L σ ϖ) :=
    (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ
  rw [mem_maximalIdeal_pow_iff hσϖ, mem_maximalIdeal_pow_iff hϖ, ← map_pow,
    map_dvd_iff (integerAlgEquiv K L σ)]

theorem algEquiv_eq_one_of_forall_integer {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝒪[L], integerAlgEquiv K L σ x = x) : σ = 1 := by
  ext y
  rw [AlgEquiv.one_apply]
  by_cases hy : valuation L y ≤ 1
  · exact congrArg Subtype.val (h ⟨y, hy⟩)
  · have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hinv : valuation L y⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hy))
    have := congrArg Subtype.val (h ⟨y⁻¹, hinv⟩)
    simp only [coe_integerAlgEquiv_apply, map_inv₀] at this
    exact inv_injective this

end Action

def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1).toNat}
  one_mem' x := by simp
  mul_mem' {σ τ} hσ hτ x := by
    have h : integerAlgEquiv K L (σ * τ) x - x =
        (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
          (integerAlgEquiv K L τ x - x) := by
      rw [map_mul, AlgEquiv.mul_apply]; ring
    rw [h]
    exact add_mem (hσ _) (hτ x)
  inv_mem' {σ} hσ x := by
    have h := hσ (integerAlgEquiv K L σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply] at h
    rw [← neg_sub]
    exact neg_mem h

variable {K L}

theorem mem_lowerRamificationGroup_iff {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1).toNat :=
  Iff.rfl

theorem mem_lowerRamificationGroup_natCast_iff {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (n + 1) := by
  rw [mem_lowerRamificationGroup_iff]
  have : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [this]

variable (K L)

theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup K L) := by
  intro i j hij σ hσ x
  exact Ideal.pow_le_pow_right (by omega) (hσ x)

theorem lowerRamificationGroup_eq_top {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup K L i = ⊤ := by
  refine eq_top_iff.mpr fun σ _ x ↦ ?_
  have : (i + 1).toNat = 0 := by omega
  rw [this, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

instance lowerRamificationGroup_normal (i : ℤ) : (lowerRamificationGroup K L i).Normal where
  conj_mem σ hσ τ x := by
    set y := integerAlgEquiv K L τ⁻¹ x
    have hx : x = integerAlgEquiv K L τ y := by
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    have h : integerAlgEquiv K L (τ * σ * τ⁻¹) x - x =
        integerAlgEquiv K L τ (integerAlgEquiv K L σ y - y) := by
      rw [map_sub, map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hx]
    rw [h, integerAlgEquiv_mem_maximalIdeal_pow_iff]
    exact hσ y

variable {K L}

theorem mem_maximalIdeal_pow_iff_normalizedValuation (n : ℕ) (y : 𝒪[L]) :
    y ∈ 𝓂[L] ^ n ↔ normalizedValuation L (y : L) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hv : normalizedValuation L ((ϖ ^ n : 𝒪[L]) : L) = WithZero.exp (-(n : ℤ)) := by
    rw [SubmonoidClass.coe_pow, map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]
    simp
  rw [mem_maximalIdeal_pow_iff hϖ, (Valuation.integer.integers (valuation L)).dvd_iff_le, ← hv,
    normalizedValuation_le_iff]
  rfl

theorem mem_lowerRamificationGroup_iff_valuation {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x ∈ 𝒪[L], normalizedValuation L (σ x - x) ≤ WithZero.exp (-(i + 1)) := by
  rw [mem_lowerRamificationGroup_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x ↦ ?_⟩
  · have := (mem_maximalIdeal_pow_iff_normalizedValuation _ _).mp (h ⟨x, hx⟩)
    have hc : ((integerAlgEquiv K L σ ⟨x, hx⟩ - ⟨x, hx⟩ : 𝒪[L]) : L) = σ x - x := rfl
    rw [hc] at this
    refine this.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · rcases le_or_gt (i + 1) 0 with hi | hi
    · have : (i + 1).toNat = 0 := by omega
      rw [this, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [mem_maximalIdeal_pow_iff_normalizedValuation]
      have h' := h x x.2
      have he : ((i + 1).toNat : ℤ) = i + 1 := by omega
      rw [he]
      simpa using h'

variable (K L)

theorem lowerRamificationGroup_zero : lowerRamificationGroup K L 0 = (residueAlgEquiv K L).ker := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  have : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [mem_lowerRamificationGroup_iff, this, pow_one]
  refine ⟨fun h r ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := residue_surjective r
    rw [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff]
    exact h x
  · have := h (residue 𝒪[L] x)
    rwa [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff] at this

theorem residue_integerAlgEquiv_of_mem_zero {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (x : 𝒪[L]) : residue 𝒪[L] (integerAlgEquiv K L σ x) = residue 𝒪[L] x := by
  rw [lowerRamificationGroup_zero, MonoidHom.mem_ker] at hσ
  rw [← residueAlgEquiv_residue, hσ, AlgEquiv.one_apply]

theorem exists_lowerRamificationGroup_eq_bot :
    ∃ n : ℕ, ∀ i : ℤ, n ≤ i → lowerRamificationGroup K L i = ⊥ := by
  have key : ∀ σ : L ≃ₐ[K] L, ∃ m : ℕ, σ ≠ 1 → σ ∉ lowerRamificationGroup K L m := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun h ↦ (h hσ).elim⟩
    obtain ⟨x, hx⟩ : ∃ x : 𝒪[L], integerAlgEquiv K L σ x ≠ x := by
      by_contra! h
      exact hσ (algEquiv_eq_one_of_forall_integer h)
    have hd : integerAlgEquiv K L σ x - x ≠ 0 := sub_ne_zero.mpr hx
    have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (𝓂[L]) (Ideal.IsPrime.ne_top')
    obtain ⟨m, hm⟩ : ∃ m : ℕ, integerAlgEquiv K L σ x - x ∉ 𝓂[L] ^ m := by
      by_contra! h
      exact hd (by
        have : integerAlgEquiv K L σ x - x ∈ ⨅ m : ℕ, 𝓂[L] ^ m := Submodule.mem_iInf _ |>.mpr h
        rwa [hinf, Ideal.mem_bot] at this)
    refine ⟨m, fun _ hmem ↦ hm ?_⟩
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (mem_lowerRamificationGroup_natCast_iff.mp hmem x)
  choose f hf using key
  obtain ⟨N, hN⟩ := Finite.exists_le f
  refine ⟨N, fun i hi ↦ eq_bot_iff.mpr fun σ hσ ↦ ?_⟩
  by_contra h
  exact hf σ h (lowerRamificationGroup_antitone K L (by have := hN σ; omega) hσ)

end GroundTheory.LocalField
