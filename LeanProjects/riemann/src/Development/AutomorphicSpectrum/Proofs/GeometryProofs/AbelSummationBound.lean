import Mathlib

open Finset

namespace GlobalTheory.CompanionTheory.AbelBounds

theorem abel_nat (a D : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ range (n + 1), -a p * D p =
      ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k)
        + a n * (-∑ k ∈ range (n + 1), D k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 := sum_range_succ (fun p => (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k)) n
    have e2 := sum_range_succ D (n + 1)
    rw [sum_range_succ (fun p => -a p * D p) (n + 1), ih, e1, e2]
    ring

theorem sum_diff (a : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ range n, (a p - a (p + 1)) = a 0 - a n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

theorem abel_bound_nat (a D : ℕ → ℝ) (n : ℕ) (Up Lo Cc : ℝ) (hUp : 0 ≤ Up) (hLo : 0 ≤ Lo)
    (hmono : ∀ p, p < n → a (p + 1) ≤ a p) (h0 : |a 0| ≤ 2) (hn : |a n| ≤ 2)
    (hY : ∀ p, p < n → -Lo ≤ -∑ k ∈ range (p + 1), D k ∧ -∑ k ∈ range (p + 1), D k ≤ Up)
    (hC : |∑ k ∈ range (n + 1), D k| ≤ Cc) :
    -(4 * Lo + 2 * Cc) ≤ ∑ p ∈ range (n + 1), -a p * D p ∧
      ∑ p ∈ range (n + 1), -a p * D p ≤ 4 * Up + 2 * Cc := by
  rw [abel_nat]
  have htel := sum_diff a n
  have hdiff : a 0 - a n ≤ 4 := by
    have := (abs_le.mp h0).2
    have := (abs_le.mp hn).1
    linarith
  have hup : ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k) ≤ 4 * Up := by
    calc ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k)
        ≤ ∑ p ∈ range n, (a p - a (p + 1)) * Up := by
          refine sum_le_sum fun p hp => ?_
          have hp' := mem_range.mp hp
          exact mul_le_mul_of_nonneg_left (hY p hp').2 (sub_nonneg.mpr (hmono p hp'))
      _ = (a 0 - a n) * Up := by rw [← sum_mul, htel]
      _ ≤ 4 * Up := mul_le_mul_of_nonneg_right hdiff hUp
  have hlo : -(4 * Lo) ≤ ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k) := by
    calc -(4 * Lo) ≤ (a 0 - a n) * (-Lo) := by nlinarith
      _ = ∑ p ∈ range n, (a p - a (p + 1)) * (-Lo) := by rw [← sum_mul, htel]
      _ ≤ ∑ p ∈ range n, (a p - a (p + 1)) * (-∑ k ∈ range (p + 1), D k) := by
          refine sum_le_sum fun p hp => ?_
          have hp' := mem_range.mp hp
          exact mul_le_mul_of_nonneg_left (hY p hp').1 (sub_nonneg.mpr (hmono p hp'))
  have hlast : |a n * (-∑ k ∈ range (n + 1), D k)| ≤ 2 * Cc := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul hn hC (abs_nonneg _) (by norm_num)
  have := abs_le.mp hlast
  constructor <;> linarith [this.1, this.2]

noncomputable def ext0 {N : ℕ} (f : Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k < N then f ⟨k, h⟩ else 0

theorem extendByZeroOnSubset_apply_coe {N : ℕ} (f : Fin N → ℝ) (k : Fin N) : ext0 f k = f k := by
  simp [ext0]

theorem sum_Iic_ext_zero {N : ℕ} (D : Fin N → ℝ) (p : Fin N) :
    ∑ k ∈ Finset.Iic p, D k = ∑ k ∈ range ((p : ℕ) + 1), ext0 D k := by
  refine sum_nbij (fun k => (k : ℕ)) ?_ ?_ ?_ ?_
  · intro k hk
    have : k ≤ p := Finset.mem_Iic.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le this)
  · intro x _ y _ h
    exact Fin.ext h
  · intro k hk
    have hk' : k < (p : ℕ) + 1 := mem_range.mp (by simpa using hk)
    have hkN : k < N := lt_of_le_of_lt (Nat.le_of_lt_succ hk') p.2
    refine ⟨⟨k, hkN⟩, ?_, rfl⟩
    simp only [Finset.coe_Iic, Set.mem_Iic]
    exact Fin.mk_le_of_le_val (Nat.le_of_lt_succ hk')
  · intro k _
    exact (extendByZeroOnSubset_apply_coe D k).symm

theorem abel_bound : ∀ (N : ℕ) (a D : Fin N → ℝ) (Up Lo Cc : ℝ), 0 ≤ Up → 0 ≤ Lo → 0 ≤ Cc →
    (∀ p q, p ≤ q → a q ≤ a p) → (∀ p, |a p| ≤ 2) →
    (∀ p : Fin N, (p : ℕ) + 1 < N → -Lo ≤ -∑ k ∈ Finset.Iic p, D k ∧
      -∑ k ∈ Finset.Iic p, D k ≤ Up) →
    (∀ p : Fin N, (p : ℕ) + 1 = N → |∑ k ∈ Finset.Iic p, D k| ≤ Cc) →
    -(4 * Lo + 2 * Cc) ≤ ∑ p, -a p * D p ∧ ∑ p, -a p * D p ≤ 4 * Up + 2 * Cc := by
  intro N a D Up Lo Cc hUp hLo hCc hmono hbd hY hC
  rcases N with _ | n
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    constructor <;> linarith
  have hsum : ∑ p, -a p * D p = ∑ p ∈ range (n + 1), -ext0 a p * ext0 D p := by
    rw [← Fin.sum_univ_eq_sum_range (fun p => -ext0 a p * ext0 D p)]
    exact sum_congr rfl fun p _ => by rw [extendByZeroOnSubset_apply_coe, extendByZeroOnSubset_apply_coe]
  rw [hsum]
  have hlt : ∀ p, p < n → p < n + 1 := fun p hp => Nat.lt_succ_of_lt hp
  refine abel_bound_nat (ext0 a) (ext0 D) n Up Lo Cc hUp hLo ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have e1 := extendByZeroOnSubset_apply_coe a ⟨p, hlt p hp⟩
    have e2 := extendByZeroOnSubset_apply_coe a ⟨p + 1, Nat.succ_lt_succ hp⟩
    simp only at e1 e2
    rw [e1, e2]
    exact hmono _ _ (Fin.mk_le_mk.mpr (Nat.le_succ p))
  · have e := extendByZeroOnSubset_apply_coe a ⟨0, Nat.succ_pos n⟩
    simp only at e
    rw [e]
    exact hbd _
  · have e := extendByZeroOnSubset_apply_coe a ⟨n, Nat.lt_succ_self n⟩
    simp only at e
    rw [e]
    exact hbd _
  · intro p hp
    have h := hY ⟨p, hlt p hp⟩ (Nat.succ_lt_succ hp)
    rw [sum_Iic_ext_zero] at h
    exact h
  · have h := hC ⟨n, Nat.lt_succ_self n⟩ rfl
    rw [sum_Iic_ext_zero] at h
    exact h

end GlobalTheory.CompanionTheory.AbelBounds
