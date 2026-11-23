import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.DifferentGalois
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_add_two_mul_card_inf_le_of_not_le {G : Type} [Group G] [Finite G] (H J : Subgroup G)
    (h : ¬ H ≤ J) : Nat.card ↥H + 2 * Nat.card ↥(H ⊓ J) ≤ 2 * Nat.card ↥H := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : H ⊓ J ≤ H)
  have hpos : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have hposH : 0 < Nat.card ↥H := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply h
    have he := Subgroup.eq_of_le_of_card_ge (inf_le_left : H ⊓ J ≤ H) (by rw [hk, mul_one])
    rw [← he]
    exact inf_le_right
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  nlinarith

open Classical in

theorem ite_add_two_mul_card_inf_sub_one_le {G : Type} [Group G] [Finite G] (H J : Subgroup G) :
    (if H ≤ J then 0 else Nat.card ↥H) + 2 * (Nat.card ↥(H ⊓ J) - 1) ≤ 2 * (Nat.card ↥H - 1) := by
  have h1 : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have h2 : Nat.card ↥(H ⊓ J) ≤ Nat.card ↥H := Subgroup.card_le_of_le inf_le_left
  split_ifs with h
  · omega
  · have := card_add_two_mul_card_inf_le_of_not_le H J h
    omega

theorem jumpSum_add_two_mul_differentExponent_fixedField_le (F L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L]
    [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)) :
    jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤
      2 * differentExponent F L := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot F L
  have hcard : ∀ i : ℤ, Nat.card ↥(lowerRamificationGroup (↥(IntermediateField.fixedField J)) L i) =
      Nat.card ↥(lowerRamificationGroup F L i ⊓ J) := by
    intro i
    rw [← lowerRamificationGroup_map_fixedField J i,
      Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective F)]
  have hFbot : lowerRamificationGroup F L ((N + 1 : ℕ) : ℤ) = ⊥ := hN _ (by push_cast; omega)
  have hMbot : lowerRamificationGroup (↥(IntermediateField.fixedField J)) L ((N + 1 : ℕ) : ℤ) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (AlgEquiv.restrictScalarsHom_injective F),
      lowerRamificationGroup_map_fixedField, hFbot, bot_inf_eq]
  have hjs : jumpSum (wild F L) ⊤ J = ∑ t ∈ Finset.range N,
      (if lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ) ≤ J then 0
        else Nat.card ↥(lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ))) := by
    unfold jumpSum
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [wild, top_inf_eq, Nat.cast_add, Nat.cast_one]
    · intro t ht
      rw [Function.mem_support] at ht
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      apply ht
      simp only [wild, top_inf_eq]
      rw [hN _ (by omega)]
      simp
  rw [hjs, differentExponent_eq_sum_card_lowerRamificationGroup F L hFbot,
    differentExponent_eq_sum_card_lowerRamificationGroup _ L hMbot,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [hcard]
  have hterm := Finset.sum_le_sum (s := Finset.range N) fun t _ =>
    ite_add_two_mul_card_inf_sub_one_le (lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ)) J
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hterm
  have h0 : Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ) ⊓ J) - 1 ≤
      Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ)) - 1 :=
    Nat.sub_le_sub_right (Subgroup.card_le_of_le inf_le_left) 1
  rw [mul_add, mul_add]
  omega

end GlobalTheory.PMon.Ram
