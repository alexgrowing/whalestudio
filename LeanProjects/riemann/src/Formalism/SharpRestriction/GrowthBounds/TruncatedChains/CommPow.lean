import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPair

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem comm_pow {R : Type*} [Ring R] {x y z : R} (h : x * y = y * x + z) (hz : z * y = y * z) (k : ℕ) :
    x * y ^ (k + 1) = y ^ (k + 1) * x + (k + 1) • (y ^ k * z) := by
  induction k with
  | zero => simp [h]
  | succ k ih =>
    calc x * y ^ (k + 1 + 1) = (x * y ^ (k + 1)) * y := by rw [pow_succ y (k + 1), mul_assoc]
      _ = (y ^ (k + 1) * x + (k + 1) • (y ^ k * z)) * y := by rw [ih]
      _ = y ^ (k + 1) * (x * y) + (k + 1) • (y ^ k * (z * y)) := by
          simp only [add_mul, smul_mul_assoc, mul_assoc]
      _ = y ^ (k + 1) * (y * x + z) + (k + 1) • (y ^ k * (y * z)) := by rw [h, hz]
      _ = y ^ (k + 1 + 1) * x + (k + 1 + 1) • (y ^ (k + 1) * z) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, ← mul_assoc (y ^ k) y z, ← pow_succ,
            succ_nsmul (y ^ (k + 1) * z) (k + 1)]
          first
          | abel
          | rw [add_assoc, add_comm (y ^ (k + 1) * z)]

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cA (K : Type*) [Field K] (s k : ℕ) : K :=
  (-1 : K) ^ k / ((Nat.choose (s + k) k : ℕ) : K) * (((k.factorial : K)⁻¹) * ((k.factorial : K)⁻¹))

theorem pf_eq (E : GLOps n K V) (a b : Fin n) (s T : ℕ) :
    pf E a b s T = ∑ k ∈ Finset.range (T + 1), cA K s k • ((E b a) ^ k * (E a b) ^ k) := by
  first
  | simp only [pf, cA]
  | unfold pf cA
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold divPowE
  first
  | rw [smul_mul_smul_comm, smul_smul]
  | simp only [smul_mul_smul_comm, smul_smul]
  | simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  | simp [smul_smul, mul_assoc, mul_comm, mul_left_comm]

theorem cA_succ [CharZero K] (s k : ℕ) :
    ((k + 1 : ℕ) : K) * cA K s (k + 1) = - ((s : K) + 1)⁻¹ * cA K (s + 1) k := by
  have hk : ((k : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hs : ((s : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero s
  have hf : ((k.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h2 : ((Nat.choose (s + 1 + k) k : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'

  have hc : ((Nat.choose (s + (k + 1)) (k + 1) : ℕ) : K)
      = ((Nat.choose (s + 1 + k) k : ℕ) : K) * ((s : K) + 1) / ((k : K) + 1) := by
    rw [eq_div_iff hk]
    have h := Nat.choose_succ_right_eq (s + k + 1) k
    have e3 : s + k + 1 - k = s + 1 := by omega
    rw [e3] at h
    have e1 : s + (k + 1) = s + k + 1 := by omega
    have e2 : s + 1 + k = s + k + 1 := by omega
    rw [e1, e2]
    exact_mod_cast h
  unfold cA
  rw [hc, Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem cross_ab [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (s T : ℕ) (hnil : (E a b) ^ T = 0) :
    E b c * pf E a b s T = pf E a b s T * E b c + ((s : K) + 1)⁻¹ • (E b a * pf E a b (s + 1) T * E a c) := by
  have hrel := hE.1
  have hYF : E b c * E b a = E b a * E b c := by
    have h := hrel b c b a
    rw [if_neg (Ne.symm hbc), if_neg hab, sub_zero, sub_eq_zero] at h
    exact h
  have hYX : E b c * E a b = E a b * E b c + -(E a c) := by
    have h := hrel b c a b
    rw [if_neg (Ne.symm hac), if_pos rfl, zero_sub] at h
    rw [← h]; abel
  have hZX : -(E a c) * E a b = E a b * -(E a c) := by
    have h := hrel a c a b
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hab), sub_zero, sub_eq_zero] at h
    rw [neg_mul, mul_neg, h]
  have hFc : ∀ k : ℕ, E b c * E b a ^ k = E b a ^ k * E b c := fun k =>
    (Commute.pow_right (hYF : Commute (E b c) (E b a)) k).eq
  have hpow : ∀ j : ℕ, E b c * E a b ^ (j + 1) =
      E a b ^ (j + 1) * E b c - ((j + 1 : ℕ) : K) • (E a b ^ j * E a c) := by
    intro j
    rw [comm_pow hYX hZX j, Nat.cast_smul_eq_nsmul, mul_neg, smul_neg, sub_eq_add_neg]
  have hT : ∀ j : ℕ, E b c * (E b a ^ (j + 1) * E a b ^ (j + 1)) =
      (E b a ^ (j + 1) * E a b ^ (j + 1)) * E b c -
        ((j + 1 : ℕ) : K) • (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    intro j
    rw [← mul_assoc, hFc, mul_assoc (E b a ^ (j + 1)) (E b c), hpow j, mul_sub, mul_smul_comm]
    simp only [mul_assoc]
  rw [pf_eq, pf_eq]
  have hL : E b c * (∑ k ∈ Finset.range (T + 1), cA K s k • (E b a ^ k * E a b ^ k)) -
      (∑ k ∈ Finset.range (T + 1), cA K s k • (E b a ^ k * E a b ^ k)) * E b c =
        -∑ j ∈ Finset.range T, (cA K s (j + 1) * ((j + 1 : ℕ) : K)) •
          (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_range_succ',
      ← Finset.sum_neg_distrib]
    have h0 : E b c * (cA K s 0 • (E b a ^ 0 * E a b ^ 0)) - cA K s 0 • (E b a ^ 0 * E a b ^ 0) * E b c = 0 := by
      simp only [pow_zero, mul_one, mul_smul_comm, smul_mul_assoc, one_mul, sub_self]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hT j, smul_sub, sub_sub_cancel_left, smul_smul]
  have hR : ((s : K) + 1)⁻¹ • (E b a * (∑ k ∈ Finset.range (T + 1), cA K (s + 1) k • (E b a ^ k * E a b ^ k)) *
      E a c) = ∑ j ∈ Finset.range T, (((s : K) + 1)⁻¹ * cA K (s + 1) j) •
        (E b a ^ (j + 1) * E a b ^ j * E a c) := by
    rw [Finset.sum_range_succ, hnil, mul_zero, smul_zero, add_zero, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, ← mul_assoc, ← pow_succ']
  rw [← sub_eq_iff_eq_add', hL, hR, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  rw [mul_comm (cA K s (j + 1)), cA_succ, neg_mul, neg_neg]

theorem cross_ac [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (u T : ℕ) (hnil : (E a c) ^ T = 0) :
    E b c * pf E a c u T = pf E a c u T * E b c - ((u : K) + 1)⁻¹ • (E b a * pf E a c (u + 1) T * E a c) := by
  have hrel := hE.1
  have hYX : E b c * E a c = E a c * E b c := by
    have h := hrel b c a c
    rw [if_neg (Ne.symm hac), if_neg (Ne.symm hbc), sub_zero, sub_eq_zero] at h
    exact h
  have hYF : E b c * E c a = E c a * E b c + E b a := by
    have h := hrel b c c a
    rw [if_pos rfl, if_neg hab, sub_zero] at h
    rw [← h]; abel
  have hEF : E b a * E c a = E c a * E b a := by
    have h := hrel b a c a
    rw [if_neg hac, if_neg hab, sub_zero, sub_eq_zero] at h
    exact h
  have hXc : ∀ k : ℕ, E b c * E a c ^ k = E a c ^ k * E b c := fun k =>
    (Commute.pow_right (hYX : Commute (E b c) (E a c)) k).eq
  have hEFk : ∀ k : ℕ, E b a * E c a ^ k = E c a ^ k * E b a := fun k =>
    (Commute.pow_right (hEF : Commute (E b a) (E c a)) k).eq
  have hEF' : ∀ (k : ℕ) (M : Module.End K V), E b a * (E c a ^ k * M) = E c a ^ k * (E b a * M) := by
    intro k M
    rw [← mul_assoc, hEFk k, mul_assoc]
  have hpow : ∀ j : ℕ, E b c * E c a ^ (j + 1) =
      E c a ^ (j + 1) * E b c + ((j + 1 : ℕ) : K) • (E c a ^ j * E b a) := by
    intro j
    rw [comm_pow hYF hEF j, Nat.cast_smul_eq_nsmul]
  have hT : ∀ j : ℕ, E b c * (E c a ^ (j + 1) * E a c ^ (j + 1)) =
      (E c a ^ (j + 1) * E a c ^ (j + 1)) * E b c +
        ((j + 1 : ℕ) : K) • (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    intro j
    rw [← mul_assoc, hpow j, add_mul, smul_mul_assoc]
    simp only [mul_assoc, hXc]
  rw [pf_eq, pf_eq]
  have hL : E b c * (∑ k ∈ Finset.range (T + 1), cA K u k • (E c a ^ k * E a c ^ k)) -
      (∑ k ∈ Finset.range (T + 1), cA K u k • (E c a ^ k * E a c ^ k)) * E b c =
        ∑ j ∈ Finset.range T, (cA K u (j + 1) * ((j + 1 : ℕ) : K)) •
          (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
    have h0 : E b c * (cA K u 0 • (E c a ^ 0 * E a c ^ 0)) - cA K u 0 • (E c a ^ 0 * E a c ^ 0) * E b c = 0 := by
      simp only [pow_zero, mul_one, mul_smul_comm, smul_mul_assoc, one_mul, sub_self]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, hT j, smul_add, add_sub_cancel_left, smul_smul]
  have hR : ((u : K) + 1)⁻¹ • (E b a * (∑ k ∈ Finset.range (T + 1), cA K (u + 1) k • (E c a ^ k * E a c ^ k)) *
      E a c) = ∑ j ∈ Finset.range T, (((u : K) + 1)⁻¹ * cA K (u + 1) j) •
        (E c a ^ j * E b a * E a c ^ (j + 1)) := by
    rw [Finset.sum_range_succ, hnil, mul_zero, smul_zero, add_zero, Finset.mul_sum, Finset.sum_mul,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, ← mul_assoc, hEFk j, mul_assoc (E c a ^ j * E b a),
      ← pow_succ]
  rw [sub_eq_add_neg, ← sub_eq_iff_eq_add', hL, hR, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← neg_smul]
  congr 1
  rw [mul_comm (cA K u (j + 1)), cA_succ, neg_mul]

end

end Formalism.MainNotions.G.ExtremalProjector
