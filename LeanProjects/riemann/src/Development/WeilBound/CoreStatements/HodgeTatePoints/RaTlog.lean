import Mathlib

open scoped Matrix TensorProduct
open Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

open Polynomial

def logPoly {O : Type} [CommRing O] (p : ℕ) (c : ℕ → O) : O[X] :=
  ∑ k ∈ Finset.Ico 1 p, C ((-1) ^ (k - 1) * c k) * X ^ k

lemma logPoly_deriv {O : Type} [CommRing O] (p : ℕ) (hp : 1 ≤ p) (c : ℕ → O)
    (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) :
    (1 + X) * derivative (logPoly p c) = 1 - (-X) ^ (p - 1) := by
  have h1 : derivative (logPoly p c) = ∑ i ∈ Finset.range (p - 1), (-X : O[X]) ^ i := by
    rw [logPoly, derivative_sum, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [derivative_C_mul_X_pow, mul_assoc, hc _ (by omega) (by omega), mul_one,
      show 1 + i - 1 = i by omega, neg_pow (X : O[X])]
    simp
  rw [h1, ← mul_neg_geom_sum, sub_neg_eq_add]

lemma logPoly_dvd {O : Type} [CommRing O] [IsDomain O] [CharZero O] (p : ℕ) (hp : 1 ≤ p)
    (c : ℕ → O) (hc : ∀ k, 1 ≤ k → k < p → c k * k = 1) (a : ℕ) :
    X ^ p ∣ (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c := by
  set P := (logPoly p c).comp ((1 + X) ^ a - 1) - C (a : O) * logPoly p c with hP
  set s : O[X] := (1 + X) ^ a - 1 with hs
  have hXs : X ∣ s := by
    have := sub_dvd_pow_sub_pow (1 + X : O[X]) 1 a
    simpa using this
  have hd := logPoly_deriv p hp c hc
  have hd2 : (1 + s) * (derivative (logPoly p c)).comp s = 1 - (-s) ^ (p - 1) := by
    have := congrArg (fun q => q.comp s) hd
    simpa using this
  have hds : (1 + X) * derivative s = C (a : O) * (1 + s) := by
    rw [hs]
    rcases a with _ | a
    · simp
    · simp only [derivative_sub, derivative_one, sub_zero, derivative_pow_succ, derivative_add,
        derivative_X, zero_add, mul_one, add_sub_cancel]
      push_cast
      ring
  have hP' : (1 + X) * derivative P = C (a : O) * ((-X) ^ (p - 1) - (-s) ^ (p - 1)) := by
    rw [hP, derivative_sub, derivative_comp, derivative_C_mul]
    linear_combination ((derivative (logPoly p c)).comp s) * hds + C (a : O) * hd2 - C (a : O) * hd
  have hdv : X ^ (p - 1) ∣ (1 + X) * derivative P := by
    rw [hP']
    exact Dvd.dvd.mul_left (dvd_sub (pow_dvd_pow_of_dvd (dvd_neg.2 dvd_rfl) _)
      (pow_dvd_pow_of_dvd (dvd_neg.2 hXs) _)) _
  have hcop : IsCoprime (X ^ (p - 1) : O[X]) (1 + X) :=
    IsCoprime.pow_left ⟨-1, 1, by ring⟩
  have hdv2 := X_pow_dvd_iff.1 (hcop.dvd_of_dvd_mul_left hdv)
  refine X_pow_dvd_iff.2 fun d hdp => ?_
  rcases d with _ | d
  · have hL : X ∣ logPoly p c := by
      refine Finset.dvd_sum fun k hk => Dvd.dvd.mul_left (dvd_pow_self _ ?_) _
      have := (Finset.mem_Ico.1 hk).1
      omega
    refine X_dvd_iff.1 (dvd_sub ?_ (hL.mul_left _))
    obtain ⟨q, hq⟩ := hL
    rw [hq, mul_comp, X_comp]
    exact hXs.mul_right _
  · have := hdv2 d (by omega)
    rw [coeff_derivative] at this
    exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast Nat.succ_ne_zero d)

section Val

variable {K : Type} [Field K] (v : Valuation K NNReal)

lemma val_nat_le (k : ℕ) : v (k : K) ≤ 1 := (natCast_mem v.integer k : (k : K) ∈ v.integer)

lemma val_nat_eq (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) (k : ℕ) (h1 : 1 ≤ k) (h2 : k < p) :
    v (k : K) = 1 := by
  by_contra hne
  have hlt : v (k : K) < 1 := lt_of_le_of_ne (val_nat_le v k) hne
  have hc : Nat.Coprime p k := (Nat.coprime_of_lt_prime (by omega) h2 Fact.out)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  have hab' : (a : K) * p + b * k = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have ha : v (a : K) ≤ 1 := (intCast_mem v.integer a : (a : K) ∈ v.integer)
  have hb : v (b : K) ≤ 1 := (intCast_mem v.integer b : (b : K) ∈ v.integer)
  have : v ((a : K) * p + b * k) < 1 := by
    refine v.map_add_lt ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right ha zero_le hp
    · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right hb zero_le hlt
  rw [hab', map_one] at this
  exact lt_irrefl _ this

lemma val_root (p : ℕ) (hp : p ≠ 0) {x : K} (hx : x ^ p = 1) : v x = 1 := by
  have : v x ^ p = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hp).1 this

lemma val_pow_sub_one {x : K} (hx : v x = 1) (k : ℕ) : v (x ^ k - 1) ≤ v (x - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x ^ (k + 1) - 1 = x * (x ^ k - 1) + (x - 1) := by ring
    rw [this]
    refine v.map_add_le ?_ le_rfl
    rw [map_mul, hx, one_mul]; exact ih

lemma val_prim (p : ℕ) [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    v (ζ - 1) ^ (p - 1) = v (p : K) := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := congrArg v hζ.prod_one_sub_pow_eq_order
  rw [map_prod] at h
  push_cast
  rw [← h, Finset.prod_congr rfl (g := fun _ => v (ζ - 1))]
  · simp
  intro k hk
  have hk' := Finset.mem_range.1 hk
  have hc : Nat.Coprime (k + 1) (n + 1) :=
    (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
  have h2 := hζ.pow_of_coprime _ hc
  rw [v.map_sub_swap]
  refine le_antisymm (val_pow_sub_one v (val_root v _ hp.ne_zero hζ.pow_eq_one) _) ?_
  obtain ⟨i, -, hi⟩ := h2.eq_pow_of_pow_eq_one hζ.pow_eq_one
  conv_lhs => rw [← hi]
  exact val_pow_sub_one v (val_root v _ hp.ne_zero h2.pow_eq_one) _

def tl (p : ℕ) (x : K) : K := ∑ k ∈ Finset.Ico 1 p, (-1) ^ (k - 1) * (x - 1) ^ k / (k : K)

lemma tl_one (p : ℕ) : tl p (1 : K) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have := (Finset.mem_Ico.1 hk).1
  rw [sub_self, zero_pow (by omega)]; simp

lemma val_tl_pow [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x : K} (hx : v x = 1)
    (a : ℕ) : v (tl p (x ^ a) - tl p x * a) ≤ v (x - 1) ^ p := by
  classical
  let c : ℕ → v.integer := fun k => if h : v (k : K) = 1 then ⟨(k : K)⁻¹, by
    rw [Valuation.mem_integer_iff, map_inv₀, h, inv_one]⟩ else 0
  have hc' : ∀ k, 1 ≤ k → k < p → (c k : K) = (k : K)⁻¹ := by
    intro k h1 h2
    simp only [c, dif_pos (val_nat_eq v p hp k h1 h2)]
  have hc : ∀ k, 1 ≤ k → k < p → c k * k = 1 := by
    intro k h1 h2
    ext
    have : (k : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast
    rw [hc' k h1 h2, inv_mul_cancel₀ this]
  have hev : ∀ t : v.integer, (((logPoly p c).eval t : v.integer) : K) = tl p (1 + (t : K)) := by
    intro t
    rw [logPoly, eval_finsetSum, tl]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    push_cast
    rw [hc' k h1 h2, add_sub_cancel_left]; ring
  obtain ⟨q, hq⟩ := logPoly_dvd p (Fact.out : p.Prime).one_le c hc a
  have hx1 : x - 1 ∈ v.integer := sub_mem (le_of_eq hx : x ∈ v.integer) (one_mem _)
  let t : v.integer := ⟨x - 1, hx1⟩
  have h := congrArg (fun r : v.integer[X] => ((r.eval t : v.integer) : K)) hq
  simp only [eval_sub, eval_comp, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at h
  push_cast at h
  rw [hev, hev] at h
  push_cast at h
  have ht : (t : K) = x - 1 := rfl
  rw [ht, add_sub_cancel, add_sub_cancel, mul_comm (a : K)] at h
  rw [h, map_mul, map_pow]
  exact mul_le_of_le_one_right zero_le (q.eval t).2

lemma val_prim_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) < 1 := by
  by_contra h
  have := one_le_pow₀ (n := p - 1) (not_lt.1 h)
  rw [val_prim v p hζ] at this
  exact absurd hp (not_lt.2 this)

lemma val_prim_pos (p : ℕ) [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : 0 < v (ζ - 1) :=
  (v.pos_iff).2 (sub_ne_zero.2 (hζ.ne_one (Fact.out : p.Prime).one_lt))

lemma val_prim_pow_le (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ p ≤ v (p : K) := by
  rw [← val_prim v p hζ]
  exact pow_le_pow_of_le_one zero_le (val_prim_lt v p hp hζ).le (Nat.sub_le _ _)

lemma val_prim_pow_lt (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (hk : 1 < k) : v (ζ - 1) ^ k < v (ζ - 1) :=
  pow_lt_self_of_lt_one₀ (val_prim_pos v p hζ) (val_prim_lt v p hp hζ) hk

lemma val_tl_prim (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (tl p ζ) = v (ζ - 1) := by
  rw [tl, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : p.Prime).one_lt]
  simp only [Nat.sub_self, pow_zero, pow_one, one_mul, Nat.cast_one, div_one]
  refine v.map_add_eq_of_lt_left (v.map_sum_lt (val_prim_pos v p hζ).ne' fun k hk => ?_)
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hk
  rw [map_div₀, val_nat_eq v p hp k (by omega) h2, div_one, map_mul, map_pow, map_pow,
    Valuation.map_neg, map_one, one_pow, one_mul]
  exact val_prim_pow_lt v p hp hζ k (by omega)

lemma val_tl_add [CharZero K] (p : ℕ) [Fact p.Prime] (hp : v (p : K) < 1) {x y : K}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : v (tl p (x * y) - tl p x - tl p y) ≤ v (p : K) := by
  have hpp : p.Prime := Fact.out
  by_cases h1 : x = 1
  · simp [h1, tl_one]
  have hζ : IsPrimitiveRoot x p := by
    have := orderOf_eq_prime hx h1
    rw [← this]; exact IsPrimitiveRoot.orderOf x
  have : NeZero p := ⟨hpp.ne_zero⟩
  obtain ⟨b, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hy
  have hv := val_root v p hpp.ne_zero hx
  have : tl p (x * x ^ b) - tl p x - tl p (x ^ b) =
      (tl p (x ^ (b + 1)) - tl p x * (b + 1 : ℕ)) - (tl p (x ^ b) - tl p x * b) := by
    rw [pow_succ']; push_cast; ring
  rw [this]
  exact (v.map_sub_le (val_tl_pow v p hp hv _) (val_tl_pow v p hp hv _)).trans
    (val_prim_pow_le v p hp hζ)

end Val

end PositivityTheory.HtPt.Ra
