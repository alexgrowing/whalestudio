import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.WindowArith

theorem sg_ineq (l n : ℕ) [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    h i + sg l h i + 1 ≤ l * (sg l h (i - 1) + 1) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hshift : ∀ j : ℕ, (h (i - 1 + ((j + 1 + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1 + 1)
      = (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) / l := by
    intro j
    have e : i - 1 + ((j + 1 + 1 : ℕ) : ZMod n) = i + ((j + 1 : ℕ) : ZMod n) := by
      push_cast; ring
    rw [e, pow_succ, div_div]
  have e0 : i - 1 + ((0 + 1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hrec : (l : ℝ) * (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
      = h i + ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
    rw [(summable_sg hl h (i - 1)).tsum_eq_zero_add, e0]
    simp only [hshift, tsum_div_const]
    field_simp
    ring
  have hS0 : 0 ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  have h1 := Nat.floor_le hS0
  have h2 := Nat.lt_floor_add_one
    (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
  have h3 := mul_lt_mul_of_pos_left h2 hl0
  have key : (h i : ℝ) + (⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ)
      < (l : ℝ) * ((⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ) + 1) := by
    linarith
  have key' : h i + ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊
      < l * (⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ + 1) := by
    exact_mod_cast key
  simp only [sg]
  omega

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ u - y := ((CharP.intCast_eq_intCast k l).mp h).symm.dvd
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by linarith, h1⟩)
  linarith

private theorem cast_ne_of_mem_cloud_of_typeG {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hG : Dt.ty i = LType.G) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ y) (hy2 : y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) :
    (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu y hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hG]
  exact hm

private theorem natCast_ne_of_mem_cloud_of_bd_of_mem_range {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hB : Dt.ty i = LType.Bd) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ (Dt.h i : ℤ) - y)
    (hy2 : (Dt.h i : ℤ) - y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) : (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu ((Dt.h i : ℤ) - y) hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hB]
  exact Int.ModEq.sub (Int.ModEq.refl _) hm

theorem windows : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  intro k _ l n r _ _ _ Dt hT1 hT2 hT3 i
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hT1i := hT1 i
  have ht := Dt.one_le_letterBlockLength
  have hwB : Dt.w i ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩))
  have heB : Dt.w i + Dt.t - 1 ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩))
  have factsG : Dt.ty i = LType.G → (∀ u ∈ Dt.lows i, 1 ≤ u ∧ u ≤ (Dt.η i : ℤ)) ∧
      1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i := fun hG =>
    ⟨fun u hu => Dt.lowG i hG u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowG i hG _ hwB).1,
      (Dt.lowG i hG _ heB).2⟩
  have factsBd : Dt.ty i = LType.Bd → (∀ u ∈ Dt.lows i, (Dt.h i : ℤ) - Dt.η i ≤ u ∧ u ≤ (Dt.h i : ℤ) - 1) ∧
      (Dt.h i : ℤ) - Dt.η i ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ (Dt.h i : ℤ) - 1 := fun hB =>
    ⟨fun u hu => Dt.lowBd i hB u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowBd i hB _ hwB).1,
      (Dt.lowBd i hB _ heB).2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsg := sg_ineq l n hl2 Dt.h i
    have e1 : Dt.sg l i = sg l Dt.h i := rfl
    have e2 : Dt.sg l (i - 1) = sg l Dt.h (i - 1) := rfl
    rw [e1, e2]
    zify at hsg
    linarith
  · intro u hu y hy1 hy2 he
    rcases Multiset.mem_add.1 hu with hu | hu
    · have huy : u = y := by
        cases hty : Dt.ty i
        · obtain ⟨hL, hw1, hw2⟩ := factsG hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
        · obtain ⟨hL, hw1, hw2⟩ := factsBd hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
      have key : ∃ β ∈ Dt.B i, |u - β| ≤ (Dt.sg l i : ℤ) + 2 := by
        by_cases hyw : y < Dt.w i
        · exact ⟨Dt.w i, mem_block.2 ⟨le_rfl, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        by_cases hye : Dt.w i + Dt.t - 1 < y
        · exact ⟨Dt.w i + Dt.t - 1, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        · exact ⟨y, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
      obtain ⟨β, hβ, hb⟩ := key
      have := hT2 i u hu β hβ
      linarith
    · cases hty : Dt.ty i
      · obtain ⟨-, hw1, hw2⟩ := factsG hty
        exact cast_ne_of_mem_cloud_of_typeG hT3 hty hu y (by omega) (by omega) he
      · obtain ⟨-, hw1, hw2⟩ := factsBd hty
        exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hty hu y (by omega) (by omega) he
  · intro hG
    obtain ⟨hL, hw1, hw2⟩ := factsG hG
    refine ⟨?_, ?_, hw1, hw2⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
  · intro hB
    obtain ⟨hL, hw1, hw2⟩ := factsBd hB
    have ew : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    refine ⟨?_, ?_, by rw [ew]; omega, by rw [ew]; omega⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he

end GlobalTheory.WindowArith
