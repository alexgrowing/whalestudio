import Mathlib
import GroundTheory.LocalFields.RamificationUnits

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Tame

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

def inertiaToResidueUnits : lowerRamificationGroup K L 0 →* 𝓀[L]ˣ where
  toFun σ := unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L))
  map_one' := by simp
  map_mul' σ τ := by
    rw [Subgroup.coe_mul, uniformizerRatio_mul, map_mul]
    congr 1
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L σ.2 _

theorem inertiaToResidueUnits_apply (σ : lowerRamificationGroup K L 0) :
    inertiaToResidueUnits hϖ σ = unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L)) :=
  rfl

theorem ker_inertiaToResidueUnits :
    (inertiaToResidueUnits hϖ).ker =
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, inertiaToResidueUnits_apply,
    ← MonoidHom.mem_ker, ker_unitsToResidue]
  exact (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ σ.2 1).symm

def inertiaQuotientToResidueUnits :
    lowerRamificationGroup K L 0 ⧸
        (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) →* 𝓀[L]ˣ :=
  (QuotientGroup.kerLift (inertiaToResidueUnits hϖ)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_inertiaToResidueUnits hϖ).symm).toMonoidHom

theorem inertiaQuotientToResidueUnits_injective :
    Function.Injective (inertiaQuotientToResidueUnits (K := K) hϖ) :=
  fun _ _ hab ↦ (MulEquiv.injective _) (QuotientGroup.kerLift_injective (inertiaToResidueUnits hϖ) hab)

omit hϖ

variable (K L)

theorem isCyclic_lowerRamificationGroup_zero_quotient :
    IsCyclic (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  exact isCyclic_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

theorem card_lowerRamificationGroup_zero_quotient_dvd :
    Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) ∣
        Nat.card 𝓀[L] - 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Nat.card_units 𝓀[L]]
  exact Subgroup.card_dvd_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

variable {K L}

theorem coprime_card_residueField_sub_one : Nat.Coprime (Nat.card 𝓀[L] - 1) (ringChar 𝓀[L]) := by
  let := Fintype.ofFinite 𝓀[L]
  have hq : ringChar 𝓀[L] ∣ Nat.card 𝓀[L] := by
    rw [← CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have h1 : 1 ≤ Nat.card 𝓀[L] := Nat.card_pos
  refine Nat.Coprime.symm (Nat.dvd_one.mp ?_)
  have ha := Nat.gcd_dvd_left (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have hb := Nat.gcd_dvd_right (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have := Nat.dvd_sub (ha.trans hq) hb
  rwa [Nat.sub_sub_self h1] at this

variable (K L)

theorem coprime_card_lowerRamificationGroup_zero_quotient :
    Nat.Coprime (Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0))) (ringChar 𝓀[K]) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  exact Nat.Coprime.coprime_dvd_left (card_lowerRamificationGroup_zero_quotient_dvd K L)
    coprime_card_residueField_sub_one

end Tame

section Wild

theorem pow_ringChar_eq_one_unitFiltration {n : ℕ} (hn : 1 ≤ n)
    (y : unitFiltration L n ⧸ unitFiltrationSucc L n) : y ^ ringChar 𝓀[L] = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  apply (unitFiltrationGradedEquiv hϖ hn).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]

theorem pow_ringChar_mem_lowerRamificationGroup {n : ℕ} (hn : 1 ≤ n) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L n) :
    σ ^ ringChar 𝓀[L] ∈ lowerRamificationGroup K L (n + 1 : ℕ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have h : ((⟨σ, hσ⟩ : lowerRamificationGroup K L n) ^ ringChar 𝓀[L]) ∈
      (ramificationToUnits hϖ n).ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_ringChar_eq_one_unitFiltration hn]
  rw [ker_ramificationToUnits, Subgroup.mem_subgroupOf] at h
  simpa using h

variable (K L)

theorem isPGroup_lowerRamificationGroup_one :
    IsPGroup (ringChar 𝓀[K]) (lowerRamificationGroup K L 1) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have key : ∀ k : ℕ, ∀ σ ∈ lowerRamificationGroup K L 1,
      σ ^ (ringChar 𝓀[L] ^ k) ∈ lowerRamificationGroup K L ((1 + k : ℕ) : ℤ) := by
    intro k σ hσ
    induction k with
    | zero => simpa using hσ
    | succ k ih =>
      rw [pow_succ, pow_mul, show 1 + (k + 1) = 1 + k + 1 by omega]
      exact pow_ringChar_mem_lowerRamificationGroup (by omega) ih
  intro σ
  refine ⟨N, Subtype.ext ?_⟩
  have := key N σ σ.2
  rw [hN _ (by omega), Subgroup.mem_bot] at this
  simpa using this

theorem isSolvable_lowerRamificationGroup_one : Group.IsSolvable (lowerRamificationGroup K L 1) := by
  have : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
  have := (isPGroup_lowerRamificationGroup_one K L).isNilpotent
  infer_instance

theorem isSolvable_lowerRamificationGroup_zero : Group.IsSolvable (lowerRamificationGroup K L 0) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have := isSolvable_lowerRamificationGroup_one K L
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (lowerRamificationGroup_antitone K L zero_le_one))
    (inertiaToResidueUnits hϖ) ?_
  intro σ hσ
  rw [ker_inertiaToResidueUnits, Subgroup.mem_subgroupOf] at hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

theorem isSolvable_algEquiv : Group.IsSolvable (L ≃ₐ[K] L) := by
  have := isSolvable_lowerRamificationGroup_zero K L
  have : Group.IsSolvable (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
    Group.isSolvable_of_comm fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  refine Group.isSolvable_of_ker_le_range (lowerRamificationGroup K L 0).subtype (residueAlgEquiv K L) ?_
  intro σ hσ
  rw [← lowerRamificationGroup_zero] at hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

end Wild

end GroundTheory.LocalField
