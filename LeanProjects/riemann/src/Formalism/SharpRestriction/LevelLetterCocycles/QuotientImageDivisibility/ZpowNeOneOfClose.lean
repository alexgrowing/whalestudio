import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Val

variable {LL : Type} [Field LL] (v : AddValuation LL (WithTop ℚ))

theorem v_natCast_nonneg (m : ℕ) : 0 ≤ v (m : LL) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ n ih =>
    rw [Nat.cast_succ]
    exact v.map_le_add ih v.map_one.symm.le

private theorem withTop_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  first
  | exact WithTop.coe_lt_coe.2 zero_lt_one
  | (rw [← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]; norm_num)
  | norm_num
  | simp

private theorem withTop_rat_not_one_add_one_le_one : ¬ ((1 : WithTop ℚ) + 1 ≤ 1) := by
  first
  | (rw [← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]; norm_num)
  | exact_mod_cast (by norm_num : ¬ ((1 : ℚ) + 1 ≤ 1))
  | norm_num
  | simp

private theorem le_v_sum_range_of_forall (f : ℕ → LL) (g : WithTop ℚ) (hf : ∀ i, g ≤ v (f i)) (m : ℕ) :
    g ≤ v (∑ i ∈ Finset.range m, f i) := by
  induction m with
  | zero => simp [AddValuation.map_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact v.map_le_add ih (hf n)

theorem v_intCast_nonneg (z : ℤ) : 0 ≤ v (z : LL) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · first
    | (rw [Int.cast_natCast]; exact v_natCast_nonneg v n)
    | (simp only [Int.cast_natCast]; exact v_natCast_nonneg v n)
    | (push_cast; exact v_natCast_nonneg v n)
  · first
    | (rw [Int.cast_neg, Int.cast_natCast, v.map_neg]; exact v_natCast_nonneg v n)
    | (push_cast; rw [v.map_neg]; exact v_natCast_nonneg v n)

variable {p : ℕ} (hp : p.Prime) (hv : v (p : LL) = 1)
include hp hv

theorem v_natCast_eq_zero (m : ℕ) (hm : ¬ p ∣ m) : v (m : LL) = 0 := by
  have h0 := v_natCast_nonneg v m
  refine le_antisymm (not_lt.mp fun hlt => ?_) h0
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  have hb := Nat.gcd_eq_gcd_ab p m
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at hb
  have hL : (p : LL) * (Nat.gcdA p m : LL) + (m : LL) * (Nat.gcdB p m : LL) = 1 := by
    first
    | (have h := congrArg (fun z : ℤ => (z : LL)) hb; push_cast at h; exact h.symm)
    | (have h := congrArg (Int.cast : ℤ → LL) hb; simp only [Int.cast_add, Int.cast_mul,
        Int.cast_natCast, Int.cast_one] at h; exact h.symm)
  have h1 : 0 < v ((p : LL) * (Nat.gcdA p m : LL)) := by
    rw [v.map_mul, hv]
    exact lt_of_lt_of_le withTop_zero_lt_one (le_add_of_nonneg_right (v_intCast_nonneg v _))
  have h2 : 0 < v ((m : LL) * (Nat.gcdB p m : LL)) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (v_intCast_nonneg v _))
  have h3 : min (v ((p : LL) * (Nat.gcdA p m : LL))) (v ((m : LL) * (Nat.gcdB p m : LL))) ≤
      v ((p : LL) * (Nat.gcdA p m : LL) + (m : LL) * (Nat.gcdB p m : LL)) :=
    v.map_le_add (min_le_left _ _) (min_le_right _ _)
  rw [hL, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

omit hp hv in
theorem v_eq_zero_of_close {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) : v ξ = 0 := by
  have hpos : 0 < v (ξ - 1) := lt_of_lt_of_le withTop_zero_lt_one h1
  have h0 : (0 : WithTop ℚ) ≤ v ((ξ - 1) + 1) := v.map_le_add hpos.le v.map_one.symm.le
  rw [sub_add_cancel] at h0
  refine le_antisymm (not_lt.mp fun hlt => ?_) h0
  have h3 : min (v ξ) (v (ξ - 1)) ≤ v (ξ + -(ξ - 1)) :=
    v.map_le_add (min_le_left _ _) (by rw [v.map_neg]; exact min_le_right _ _)
  have e : ξ + -(ξ - 1) = 1 := by ring
  rw [e, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min hlt hpos))

omit hp hv in
theorem v_geom_nonneg {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    0 ≤ v (∑ i ∈ Finset.range m, ξ ^ i) := by
  have hξ := v_eq_zero_of_close v h1
  exact le_v_sum_range_of_forall v (fun i => ξ ^ i) 0
    (fun i => by
      show (0 : WithTop ℚ) ≤ v (ξ ^ i)
      exact le_of_eq (by rw [v.map_pow, hξ, smul_zero])) m

omit hp hv in
theorem v_pow_sub_one {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    v (ξ - 1) ≤ v (ξ ^ m - 1) := by
  rw [← geom_sum_mul ξ m, v.map_mul]
  exact le_add_of_nonneg_left (v_geom_nonneg v h1 m)

omit hp hv in

theorem v_geom_sub {ξ : LL} (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (m : ℕ) :
    v (ξ - 1) ≤ v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : LL)) := by
  have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : LL) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
    first
    | (rw [Finset.sum_sub_distrib]; simp)
    | simp [Finset.sum_sub_distrib]
  rw [e]
  exact le_v_sum_range_of_forall v (fun i => ξ ^ i - 1) _ (fun i => v_pow_sub_one v h1 i) m

theorem pow_p_ne_one {ξ : LL} (hp3 : 3 ≤ p) (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1)) (hne : ξ ≠ 1) :
    ξ ^ p ≠ 1 := by
  intro hpow
  have hS : (∑ i ∈ Finset.range p, ξ ^ i) = 0 := by
    have h := geom_sum_mul ξ p
    rw [hpow, sub_self] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.mp h') hne
  have eSp : (∑ i ∈ Finset.range p, ξ ^ i) - (p : LL) =
      (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) * (ξ - 1) := by
    rw [Finset.sum_mul]
    simp only [geom_sum_mul]
    first
    | (rw [Finset.sum_sub_distrib]; simp)
    | simp [Finset.sum_sub_distrib]
  have hT : 1 ≤ v (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) := by
    have e2 : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ξ ^ j) =
        (∑ i ∈ Finset.range p, ((∑ j ∈ Finset.range i, ξ ^ j) - (i : LL))) +
          (((∑ i ∈ Finset.range p, i : ℕ)) : LL) := by
      first
      | (rw [Finset.sum_sub_distrib, Nat.cast_sum]; ring)
      | (push_cast; rw [Finset.sum_sub_distrib]; ring)
    rw [e2]
    apply v.map_le_add
    · exact le_v_sum_range_of_forall v _ _ (fun i => le_trans h1 (v_geom_sub v h1 i)) p
    · obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := hp.eq_two_or_odd'.resolve_left (by omega)
      have hs : (∑ i ∈ Finset.range p, i) = p * k := by
        apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
        rw [Finset.sum_range_id_mul_two, hk, Nat.add_sub_cancel]
        ring
      rw [hs, Nat.cast_mul, v.map_mul, hv]
      exact le_add_of_nonneg_right (v_natCast_nonneg v k)
  have hvS : 1 + 1 ≤ v ((∑ i ∈ Finset.range p, ξ ^ i) - (p : LL)) := by
    rw [eSp, v.map_mul]
    exact add_le_add hT h1
  rw [hS, zero_sub, v.map_neg, hv] at hvS
  exact withTop_rat_not_one_add_one_le_one hvS

theorem pow_ne_one_of_close (hp3 : 3 ≤ p) :
    ∀ (m : ℕ) (ξ : LL), 0 < m → (1 : WithTop ℚ) ≤ v (ξ - 1) → ξ ≠ 1 → ξ ^ m ≠ 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro ξ hm h1 hne
    by_cases hpm : p ∣ m
    · obtain ⟨k, rfl⟩ := hpm
      have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      have hlt : k < p * k := by
        have : 1 < p := hp.one_lt
        nlinarith
      rw [pow_mul]
      exact ih k hlt (ξ ^ p) hk (le_trans h1 (v_pow_sub_one v h1 p))
        (pow_p_ne_one v hp hv hp3 h1 hne)
    · intro hpow
      have hS : (∑ i ∈ Finset.range m, ξ ^ i) = 0 := by
        have h := geom_sum_mul ξ m
        rw [hpow, sub_self] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd (sub_eq_zero.mp h') hne
      have h2 := v_geom_sub v h1 m
      rw [hS, zero_sub, v.map_neg, v_natCast_eq_zero v hp hv m hpm] at h2
      exact absurd (le_trans h1 h2) (not_le.mpr withTop_zero_lt_one)

theorem zpow_ne_one_of_close (hp3 : 3 ≤ p) (ξ : LL) (h1 : (1 : WithTop ℚ) ≤ v (ξ - 1))
    (hne : ξ ≠ 1) (k : ℤ) (hk : k ≠ 0) : ξ ^ k ≠ 1 := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · have hn : 0 < n := by omega
    rw [zpow_natCast]
    exact pow_ne_one_of_close v hp hv hp3 n ξ hn h1 hne
  · have hn : 0 < n := by omega
    rw [zpow_neg, zpow_natCast, Ne, inv_eq_one]
    exact pow_ne_one_of_close v hp hv hp3 n ξ hn h1 hne

end Formalism.MainNotions.N.Pv.LocalLengthBound.Val
