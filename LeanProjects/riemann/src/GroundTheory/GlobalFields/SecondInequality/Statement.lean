import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap

namespace GroundTheory.Global

open NumberField Module Polynomial IntermediateField

section GroupTheory

variable {G G' : Type*} [Group G] [Group G']

theorem enatCard_quotient_le_iff (H : Subgroup G) (n : ℕ) :
    ENat.card (G ⧸ H) ≤ n ↔ H.index ≠ 0 ∧ H.index ≤ n := by
  by_cases hf : Finite (G ⧸ H)
  · rw [ENat.card_eq_coe_natCard, Nat.cast_le]
    exact ⟨fun h ↦ ⟨Subgroup.index_ne_zero_of_finite, h⟩, fun h ↦ h.2⟩
  · have : Infinite (G ⧸ H) := not_finite_iff_infinite.1 hf
    rw [ENat.card_eq_top_of_infinite]
    refine ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd h.1 ?_⟩
    rw [not_not, Subgroup.index, Nat.card_eq_zero_of_infinite]

theorem index_le_of_comap_le (f : G →* G') {H : Subgroup G} {H' : Subgroup G'}
    (hle : H'.comap f ≤ H) (hH' : H'.index ≠ 0) : H.index ≠ 0 ∧ H.index ≤ H'.index := by
  have h1 : (H'.comap f).index ≤ H'.index := by
    rw [Subgroup.index_comap, ← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top (by rwa [Subgroup.relIndex_top_right])
  have h2 : (H'.comap f).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact mt (Subgroup.relIndex_eq_zero_of_le_right le_top) (by rwa [Subgroup.relIndex_top_right])
  have h3 : H.index ∣ (H'.comap f).index := Subgroup.index_dvd_of_le hle
  exact ⟨fun h ↦ h2 (Nat.eq_zero_of_zero_dvd (h ▸ h3)), (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h3).trans h1⟩

theorem index_map_le (f : G →* G') {H : Subgroup G} (hH : H.index ≠ 0) (hf : f.range.index ≠ 0) :
    (H.map f).index ≠ 0 ∧ (H.map f).index ≤ f.range.index * H.index := by
  have h3 : (H ⊔ f.ker).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h4 : (H ⊔ f.ker).index ≠ 0 := fun h ↦ hH (Nat.eq_zero_of_zero_dvd (h ▸ h3))
  rw [Subgroup.index_map]
  refine ⟨mul_ne_zero h4 hf, ?_⟩
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hH) h3)

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {x : G} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ∈ H := by
  have hg : ((a.gcd b : ℕ) : ℤ) = a * a.gcdA b + b * a.gcdB b := Nat.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at hg
  have : x = (x ^ a) ^ a.gcdA b * (x ^ b) ^ a.gcdB b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  rw [this]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem mul_comm_of_isCyclic [IsCyclic G] (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
  exact zpow_mul_comm g i j

end GroupTheory

def SecondInequalityRoots.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (p : ℕ), p.Prime → HasEnoughRootsOfUnity K p →
    Module.finrank K L = p → ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ p

section Norms

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem pow_finrank_mem_range_ideleClassNorm (c : IdeleClassGroup K) :
    c ^ finrank K L ∈ (ideleClassNorm K L).range :=
  ⟨ideleClassMap K L c, ideleClassNorm_ideleClassMap c⟩

end Norms

end GroundTheory.Global
