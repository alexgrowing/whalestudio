import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

noncomputable section

open Polynomial

namespace UpperTheory.V.Sd

private lemma lk_deriv (k : ℕ) (x : ℂ) (hx : x ≠ 1) :
    ∃ d : ℂ, HasDerivAt (fun y : ℂ => Lk (k + 1) y) d x ∧ x * d = Lk (k + 2) x := by
  have hne : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hp := Polynomial.hasDerivAt_aeval (numL (k + 1)) x
  have hq : HasDerivAt (fun y : ℂ => (1 - y) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (1 - x) ^ k * (-1)) x := by
    have h1 : HasDerivAt (fun y : ℂ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℂ)
    have h2 := h1.pow (k + 1)
    simp only [Nat.add_sub_cancel] at h2
    exact h2
  refine ⟨_, hp.div hq (pow_ne_zero _ hne), ?_⟩
  have e : numL (k + 2) = X * (derivative (numL (k + 1)) * (1 - X) + C ((k : ℤ) + 1) * numL (k + 1)) := numL.eq_3 k
  unfold Lk
  rw [e]
  simp only [map_mul, map_add, map_sub, map_one, aeval_X, aeval_C]
  field_simp
  push_cast
  ring

private lemma lk_one (w : ℕ) (hw : 1 ≤ w) (ζ x : ℂ) (hζ : IsPrimitiveRoot ζ w) (hx : x ^ w ≠ 1) :
    ∑ j ∈ Finset.range w, Lk 1 (x * ζ ^ j) = (w : ℂ) ^ 1 * Lk 1 (x ^ w) := by
  have hy : ∀ j : ℕ, (x * ζ ^ j) ^ w = x ^ w := by
    intro j
    rw [mul_pow, ← pow_mul, mul_comm j w, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hxw : 1 - x ^ w ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hne : ∀ j : ℕ, 1 - x * ζ ^ j ≠ 0 := by
    intro j h
    apply hx
    rw [← hy j, ← sub_eq_zero.mp h, one_pow]
  have term : ∀ j : ℕ, Lk 1 (x * ζ ^ j) = (∑ m ∈ Finset.range w, (x * ζ ^ j) ^ m) / (1 - x ^ w) - 1 := by
    intro j
    have g := geom_sum_mul (x * ζ ^ j) w
    rw [hy j] at g
    unfold Lk
    simp only [numL.eq_2, aeval_X, pow_one]
    rw [eq_sub_iff_add_eq, div_add_one (hne j), div_eq_div_iff (hne j) hxw]
    linear_combination g
  have inner : ∀ m ∈ Finset.range w, ∑ j ∈ Finset.range w, (x * ζ ^ j) ^ m = if m = 0 then (w : ℂ) else 0 := by
    intro m hm
    split_ifs with h0
    · simp [h0]
    · have hm' : m < w := Finset.mem_range.mp hm
      have hq : ζ ^ m ≠ 1 := hζ.pow_ne_one_of_pos_of_lt h0 hm'
      have g := geom_sum_mul (ζ ^ m) w
      rw [← pow_mul, mul_comm m w, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at g
      have hs : ∑ i ∈ Finset.range w, (ζ ^ m) ^ i = 0 := by
        rcases mul_eq_zero.mp g with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hq
      calc ∑ j ∈ Finset.range w, (x * ζ ^ j) ^ m = x ^ m * ∑ i ∈ Finset.range w, (ζ ^ m) ^ i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j m]
        _ = 0 := by rw [hs, mul_zero]
  have total : ∑ j ∈ Finset.range w, ∑ m ∈ Finset.range w, (x * ζ ^ j) ^ m = w := by
    rw [Finset.sum_comm, Finset.sum_congr rfl inner, Finset.sum_ite_eq' (Finset.range w) 0]
    simp [Finset.mem_range.mpr (by omega : 0 < w)]
  rw [Finset.sum_congr rfl (fun j _ => term j), Finset.sum_sub_distrib, ← Finset.sum_div, total]
  unfold Lk
  simp only [numL.eq_2, aeval_X, pow_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp
  ring

theorem lkDist : LkDist := by
  intro w k hw hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro ζ x hζ hx
    exact lk_one w hw ζ x hζ hx
  | succ k hk ih =>
    intro ζ x hζ hx
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hy : ∀ j : ℕ, (x * ζ ^ j) ^ w = x ^ w := by
      intro j
      rw [mul_pow, ← pow_mul, mul_comm j w, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hne : ∀ j : ℕ, x * ζ ^ j ≠ 1 := by
      intro j h
      apply hx
      rw [← hy j, h, one_pow]
    choose d hd hdx using fun j : ℕ => lk_deriv m (x * ζ ^ j) (hne j)
    obtain ⟨e, he, hex⟩ := lk_deriv m (x ^ w) hx
    have hj : ∀ j : ℕ, HasDerivAt (fun y : ℂ => Lk (m + 1) (y * ζ ^ j)) (d j * ζ ^ j) x := by
      intro j
      exact (hd j).comp x (hasDerivAt_mul_const (ζ ^ j))
    have hF : HasDerivAt (fun y : ℂ => ∑ j ∈ Finset.range w, Lk (m + 1) (y * ζ ^ j))
        (∑ j ∈ Finset.range w, d j * ζ ^ j) x :=
      HasDerivAt.fun_sum (u := Finset.range w) (A := fun j (y : ℂ) => Lk (m + 1) (y * ζ ^ j))
        (A' := fun j => d j * ζ ^ j) (fun j _ => hj j)
    have hG : HasDerivAt (fun y : ℂ => (w : ℂ) ^ (m + 1) * Lk (m + 1) (y ^ w))
        ((w : ℂ) ^ (m + 1) * (e * ((w : ℂ) * x ^ (w - 1)))) x :=
      (he.comp x (hasDerivAt_pow w x)).const_mul _
    have hev : (fun y : ℂ => ∑ j ∈ Finset.range w, Lk (m + 1) (y * ζ ^ j)) =ᶠ[nhds x]
        (fun y : ℂ => (w : ℂ) ^ (m + 1) * Lk (m + 1) (y ^ w)) := by
      have ho : IsOpen {y : ℂ | y ^ w ≠ 1} := isOpen_ne_fun (continuous_pow w) continuous_const
      filter_upwards [ho.mem_nhds hx] with y hy'
      exact ih ζ y hζ hy'
    have heq := hF.unique (hG.congr_of_eventuallyEq hev)
    have hw' : x * x ^ (w - 1) = x ^ w := by
      rw [← pow_succ']
      congr 1
      omega
    calc ∑ j ∈ Finset.range w, Lk (m + 1 + 1) (x * ζ ^ j)
        = x * ∑ j ∈ Finset.range w, d j * ζ ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← hdx j]
          ring
      _ = (w : ℂ) ^ (m + 1 + 1) * Lk (m + 1 + 1) (x ^ w) := by
          rw [heq, ← hex, ← hw']
          ring

end UpperTheory.V.Sd
