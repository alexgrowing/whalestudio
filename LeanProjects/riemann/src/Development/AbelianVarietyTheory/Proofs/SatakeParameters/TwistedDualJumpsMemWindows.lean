import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem jT1_mem_window_of_bounded_v : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ),
    (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) →
    (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s,
    (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ)
      else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨
    |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  intro R P j s S η hv hb u hu
  obtain ⟨c, hc⟩ := R.t_odd
  have ht1 : ((R.t : ℤ) - 1) / 2 = c := by rw [hc]; push_cast; omega
  have ht2 : ((R.t : ℤ) + 1) / 2 = c + 1 := by rw [hc]; push_cast; omega
  have htc : (R.t : ℤ) = 2 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨E, hE⟩ := P.e_int j
  have hEf : ⌊P.e j⌋ = E := by rw [hE]; simp
  have hV : ∀ i, 0 ≤ ⌊P.v i⌋ ∧ ⌊P.v i⌋ ≤ ((⌊S⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨V, hVi⟩ := P.v_int i
    obtain ⟨h0, h1⟩ := hv i
    rw [hVi] at h0 h1 ⊢
    simp only [Int.floor_intCast]
    push_cast at h0 h1
    have h0' : (0:ℤ) ≤ V := by exact_mod_cast h0
    refine ⟨h0', ?_⟩
    have h2 : ((V.toNat : ℕ) : ℝ) ≤ S := by
      have : ((V.toNat : ℕ) : ℝ) = (V : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0'
      rw [this]; exact h1
    have := Nat.le_floor h2
    omega
  have hB : ∀ i, -((⌊η⌋₊ : ℕ) : ℤ) ≤ ⌊P.b i⌋ - E ∧ ⌊P.b i⌋ - E ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨B, hBi⟩ := P.b_int i
    have h1 := hb i
    rw [hBi, hE] at h1
    rw [hBi]
    simp only [Int.floor_intCast]
    have h2 : (((B - E).natAbs : ℕ) : ℝ) ≤ η := by
      rw [Nat.cast_natAbs]; push_cast at h1 ⊢; exact h1
    have h3 := Nat.le_floor h2
    have h4 : |B - E| ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    exact abs_le.mp h4
  simp only [jT1, jR, jW, cloud, lows, block, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
    Finset.mem_univ, true_and, Multiset.mem_range] at hu
  cases s with
  | true =>
    simp only [szT, if_true, Bool.not_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [if_true, Multiset.mem_map, Multiset.mem_add, Finset.mem_val, Finset.mem_univ,
      true_and] at hu
    obtain ⟨x, (hx | hx) | hx, rfl⟩ := hu
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hV i
      left; rw [hEf, ht1]; constructor <;> omega
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hB i
      right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega
  | false =>
    simp only [szT, Bool.not_false, if_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [Bool.false_eq_true, if_false, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
      Finset.mem_univ, true_and] at hu
    obtain ⟨x, hx | hx, rfl⟩ := hu
    · obtain ⟨y, hy | hy, rfl⟩ := hx
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hV i
        left; rw [hEf, ht1]; constructor <;> omega
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hB i
        right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega

end GlobalTheory
