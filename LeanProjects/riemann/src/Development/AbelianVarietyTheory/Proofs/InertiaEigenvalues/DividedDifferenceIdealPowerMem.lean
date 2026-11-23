import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfEvalNatCastAdd
open Polynomial

namespace GlobalTheory.FilCoeff

theorem poly_eq_zero_of_eval_nat {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) :
    ∀ (n : ℕ) (F : R[X]), F.natDegree ≤ n → ∀ m : ℕ,
      (∀ k : ℕ, F.eval ((m + k : ℕ) : R) = 0) → F = 0 := by
  first
  | exact @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | (apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add ..)

noncomputable def binPoly {R : Type} [CommRing R] (y : R) (s : ℕ) : R[X] :=
  ∑ j ∈ Finset.range s, C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j

theorem eval_binPoly {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (k : ℕ) :
    (binPoly y s).eval ((k : ℕ) : R) = (1 + y) ^ k := by
  have hterm : ∀ j ∈ Finset.range s,
      eval ((k : ℕ) : R) (C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j)
        = y ^ j * ((k.choose j : ℕ) : R) := by
    intro j _
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc, ← mul_assoc (Ring.inverse _),
      Ring.inverse_mul_cancel _ (hR _ (Nat.factorial_ne_zero j)), one_mul]
  rw [binPoly, eval_finsetSum, Finset.sum_congr rfl hterm, add_comm, add_pow]
  simp only [one_pow, mul_one]
  have h1 : ∑ j ∈ Finset.range s, y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [pow_eq_zero_of_le hj hy, zero_mul]
  have h2 : ∑ j ∈ Finset.range (k + 1), y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  rw [h1, h2]

theorem smul_coeff_one_eq_zero {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (c : ℕ → R)
    (h : ∀ k : ℕ, ∑ i ∈ Finset.range s, ((1 + y) ^ k - 1) ^ i * c i = 0) :
    y * c 1 = 0 := by
  rcases s with _ | _ | t
  · have h1 : (1 : R) = 0 := by simpa using hy
    calc y * c 1 = y * c 1 * 1 := (mul_one _).symm
      _ = 0 := by rw [h1, mul_zero]
  · rw [zero_add, pow_one] at hy; rw [hy, zero_mul]
  set P : R[X] := binPoly y (t + 2) - 1 with hPdef
  have hP : ∀ k : ℕ, P.eval ((k : ℕ) : R) = (1 + y) ^ k - 1 := by
    intro k; rw [hPdef, eval_sub, eval_one, eval_binPoly hR y _ hy k]
  set F : R[X] := ∑ i ∈ Finset.range (t + 2), P ^ i * C (c i) with hFdef
  have hF : F = 0 := by
    apply poly_eq_zero_of_eval_nat hR F.natDegree F le_rfl 0
    intro k
    rw [zero_add, hFdef, eval_finsetSum]
    simp only [eval_mul, eval_pow, eval_C, hP]
    exact h k
  have h0 : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]; simpa using hP 0
  obtain ⟨Q, hQ⟩ := X_dvd_iff.2 h0
  have hF1 : F.coeff 1 = Q.coeff 0 * c 1 := by
    rw [hFdef, finsetSum_coeff]
    simp only [coeff_mul_C, hQ, mul_pow, coeff_X_pow_mul']
    rw [Finset.sum_eq_single 1]
    · simp
    · intro i _ hi
      rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · have : i = 0 := by omega
        subst this; simp [coeff_one]
      · rw [if_neg (by omega), zero_mul]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hL : P.coeff 1 = Q.coeff 0 := by rw [hQ, coeff_X_mul]
  have hL2 : P.coeff 1 = y * (1 + (∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
    rw [hPdef, coeff_sub, coeff_one, if_neg one_ne_zero, sub_zero, binPoly, finsetSum_coeff]
    simp only [coeff_C_mul]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      Ring.inverse_one, descPochhammer_one, descPochhammer_zero, coeff_X_one, coeff_one,
      if_neg one_ne_zero, mul_zero, add_zero, mul_one, one_mul]
    have e : ∀ j ∈ Finset.range t, y ^ (j + 1 + 1) * Ring.inverse (((j + 1 + 1).factorial : ℕ) : R)
        * (descPochhammer R (j + 1 + 1)).coeff 1
        = y * ((y ^ j * Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
      intro j _; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hnil : IsNilpotent ((∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) :=
    (Commute.all _ y).isNilpotent_mul_left ⟨_, hy⟩
  have hc := congrArg (fun G : R[X] => G.coeff 1) hF
  simp only [hF1, coeff_zero] at hc
  rw [← hL, hL2, mul_comm, ← mul_assoc, mul_comm (c 1), mul_comm _ (1 + _)] at hc
  have := (hnil.isUnit_one_add).mul_right_eq_zero.1 hc
  rw [mul_comm] at this ⊢; exact (mul_comm (c 1) y) ▸ this

theorem d_mul_x_one_mem_span_pow :
    ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u →
      q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B),
      (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i
        ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  intro B _ hB d q u hu hq s x hx
  set I : Ideal B := Ideal.span {d ^ s} with hI
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B ⧸ I) := fun n hn => by
    simpa using (hB n hn).map (Ideal.Quotient.mk I)
  have hy : (Ideal.Quotient.mk I q - 1) ^ s = 0 := by
    rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      mul_pow]
    exact I.mul_mem_right _ (Ideal.subset_span rfl)
  have key := smul_coeff_one_eq_zero hR (Ideal.Quotient.mk I q - 1) s hy
    (fun i => Ideal.Quotient.mk I (Ring.inverse (i.factorial : B) * x i)) (by
      intro k
      rw [add_sub_cancel]
      have := (Ideal.Quotient.eq_zero_iff_mem).2 (hx k)
      rw [map_sum] at this
      simpa only [map_mul, map_pow, map_sub, map_one, mul_assoc] using this)
  simp only [Nat.factorial_one, Nat.cast_one, Ring.inverse_one, one_mul] at key
  rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at key
  obtain ⟨v, rfl⟩ := hu
  have : d * x 1 = d * ↑v * x 1 * ↑v⁻¹ := by
    rw [mul_right_comm d, mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact I.mul_mem_right _ key

end GlobalTheory.FilCoeff
