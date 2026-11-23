import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA

noncomputable section

namespace Formalism.L2.Th1.B

open PowerSeries

section Rules

variable {K : Type} [Field K] [CharZero K]

theorem dz_ofNat (n : ℕ) [n.AtLeastTwo] : dz (OfNat.ofNat n : PowerSeries K) = 0 := by
  rw [show (OfNat.ofNat n : PowerSeries K) = C (OfNat.ofNat n : K) from (map_ofNat C n).symm]
  exact PowerSeries.derivative_C

theorem dz_one : dz (1 : PowerSeries K) = 0 := by
  exact Derivation.map_one_eq_zero _

theorem dz_C (a : K) : dz (C a : PowerSeries K) = 0 := PowerSeries.derivative_C

theorem dz_X : dz (X : PowerSeries K) = 1 := PowerSeries.derivative_X

theorem dz_add (f g : PowerSeries K) : dz (f + g) = dz f + dz g := map_add _ f g

theorem dz_sub (f g : PowerSeries K) : dz (f - g) = dz f - dz g := map_sub _ f g

theorem dz_neg (f : PowerSeries K) : dz (-f) = -dz f := map_neg _ f

theorem dz_mul (f g : PowerSeries K) : dz (f * g) = f * dz g + g * dz f := by
  simp only [dz, Derivation.leibniz, smul_eq_mul]

theorem dz_two : dz (2 : PowerSeries K) = 0 := dz_ofNat 2

theorem dz_four : dz (4 : PowerSeries K) = 0 := dz_ofNat 4

theorem two_ne : (2 : PowerSeries K) ≠ 0 := by
  intro h
  have h2 := congrArg (constantCoeff (R := K)) h
  rw [map_ofNat, map_zero] at h2
  exact two_ne_zero h2

theorem dz_sq (f : PowerSeries K) : dz (f ^ 2) = 2 * f * dz f := by
  rw [pow_two, dz_mul]
  ring

theorem dz_cube (f : PowerSeries K) : dz (f ^ 3) = 3 * f ^ 2 * dz f := by
  rw [pow_succ, dz_mul, dz_sq]
  ring

theorem dz_X_pow (n : ℕ) : dz ((X : PowerSeries K) ^ (n + 1)) = ((n : PowerSeries K) + 1) * X ^ n := by
  induction n with
  | zero => simp [dz_X]
  | succ n ih =>
    rw [pow_succ, dz_mul, ih, dz_X]
    push_cast
    ring

theorem X_ne : (X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero

theorem ne_zero_of_constantCoeff {f : PowerSeries K} (h : constantCoeff f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (map_zero _)

end Rules

theorem weierstrassReducedEquations : WpReduced := by
  intro K _ _ g2 g3 P hP
  obtain ⟨_, _, hE⟩ := hP
  have E1 : X ^ 4 * dz P ^ 2 - 4 * X * dz P =
      12 * P + 12 * X ^ 2 * P ^ 2 + 4 * X ^ 4 * P ^ 3 - C g2 * X ^ 2 * (1 + X ^ 2 * P) -
        C g3 * X ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne (K := K)))
    linear_combination hE
  refine ⟨E1, ?_⟩
  have hg : (C g2 : PowerSeries K) = 2 * C (g2 / 2) := by
    rw [← map_ofNat C 2, ← map_mul]
    congr 1
    field_simp
  rw [hg] at E1
  have d4 : dz ((X : PowerSeries K) ^ 4) = 4 * X ^ 3 := by
    rw [show (X : PowerSeries K) ^ 4 = (X ^ 2) ^ 2 by ring, dz_sq, dz_sq, dz_X]
    ring
  have hdiff : 4 * X ^ 3 * dz P ^ 2 + 2 * X ^ 4 * dz P * dz (dz P) - 4 * dz P - 4 * X * dz (dz P) =
      12 * dz P + 24 * X * P ^ 2 + 24 * X ^ 2 * P * dz P + 16 * X ^ 3 * P ^ 3 +
        12 * X ^ 4 * P ^ 2 * dz P - 2 * C (g2 / 2) * (2 * X + 4 * X ^ 3 * P + X ^ 4 * dz P) -
        4 * C g3 * X ^ 3 := by
    have h := congrArg dz E1
    have c12 : dz (12 : PowerSeries K) = 0 := dz_ofNat 12
    simp only [dz_add, dz_sub, dz_mul, dz_sq, dz_cube, dz_C, dz_X, dz_two, dz_four, c12, dz_one, d4] at h
    linear_combination h
  refine mul_left_cancel₀ (?_ : (2 * X * (X ^ 3 * dz P - 2) : PowerSeries K) ≠ 0) ?_
  · refine mul_ne_zero (mul_ne_zero two_ne X_ne) (ne_zero_of_constantCoeff ?_)
    rw [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, map_ofNat]
    norm_num
  · linear_combination X ^ 2 * hdiff - 4 * X * E1

theorem invertedSecondDeriv : WSecond := by
  intro K _ _ A kap w hw
  obtain ⟨h0, h2, hE⟩ := hw
  have e1 : constantCoeff (dz w) = PowerSeries.coeff 1 w := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  have h1 : PowerSeries.coeff 1 w = 0 := by
    have hc := congrArg (constantCoeff (R := K)) hE
    simpa [e1, h0] using hc
  refine ⟨h1, ?_⟩
  have hd : dz w ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) h
    rw [PowerSeries.coeff_derivative, h2] at hc
    norm_num at hc
  have hdiff := congrArg dz hE
  simp only [dz_sq, dz_add, dz_mul, dz_cube, dz_C, dz_four] at hdiff
  refine mul_left_cancel₀ (mul_ne_zero two_ne hd) ?_
  linear_combination hdiff

theorem invertedEven : WEven := by
  intro K _ _ A kap w hw
  obtain ⟨h1, h2⟩ := invertedSecondDeriv K A kap w hw
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨m, rfl⟩ := hn
  rcases m with _ | m
  · simpa using h1
  ·
    have hk : PowerSeries.coeff (2 * m + 1) w = 0 := ih _ (by omega) ⟨m, rfl⟩
    have hsq : PowerSeries.coeff (2 * m + 1) (w ^ 2) = 0 := by
      rw [pow_two, PowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨i, j⟩ hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      simp only at hij
      rcases Nat.even_or_odd i with ⟨a, ha⟩ | hi
      · rw [ih j (by omega) ⟨m - a, by omega⟩, mul_zero]
      · rw [ih i (by omega) hi, zero_mul]
    have e : (2 + 4 * C A * w + 6 * C kap * w ^ 2 : PowerSeries K) =
        C 2 + C (4 * A) * w + C (6 * kap) * w ^ 2 := by
      simp only [map_mul, map_ofNat]
    have hc := congrArg (PowerSeries.coeff (2 * m + 1)) h2
    rw [e, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, hk, hsq,
      PowerSeries.coeff_C, if_neg (by omega)] at hc
    simp only [dz, PowerSeries.coeff_derivative] at hc
    have a1 : ((2 * m + 1 + 1 : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    have a2 : ((2 * m + 1 : ℕ) : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero _
    have hz : PowerSeries.coeff (2 * m + 1 + 1 + 1) w = 0 := by
      have hc' : PowerSeries.coeff (2 * m + 1 + 1 + 1) w * (((2 * m + 1 + 1 : ℕ) : K) + 1) *
          (((2 * m + 1 : ℕ) : K) + 1) = 0 := by
        rw [hc]
        ring
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hc').resolve_right a2)).resolve_right a1
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring]
    exact hz

theorem shiftedReciprocalInverted : WOfWp := by
  intro K _ _ g2 g3 e1 P hP he
  obtain ⟨_, _, hE⟩ := hP
  have hu : constantCoeff (1 + X ^ 2 * P - C e1 * X ^ 2) ≠ 0 := by simp
  have hw : (1 + X ^ 2 * P - C e1 * X ^ 2) * wOf e1 P = X ^ 2 := by
    rw [wOf, mul_left_comm, PowerSeries.mul_inv_cancel _ hu, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [wOf]
    simp
  · rw [wOf, PowerSeries.coeff_X_pow_mul']
    simp [PowerSeries.constantCoeff_inv]
  · have hdu : dz (1 + X ^ 2 * P - C e1 * X ^ 2) = 2 * X * P + X ^ 2 * dz P - 2 * C e1 * X := by
      simp only [dz_add, dz_sub, dz_mul, dz_one, dz_C, dz_X, dz_sq]
      ring
    have hd := congrArg dz hw
    rw [dz_mul, hdu, dz_sq, dz_X] at hd

    have hA : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -X * (X ^ 3 * dz P - 2) := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) * hd - (2 * X * P + X ^ 2 * dz P - 2 * C e1 * X) * hw
    have h1 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P = X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * hw
    have h2 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 2 = X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2) * hw
    have h3 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 3 = X ^ 6 * (1 + X ^ 2 * P - C e1 * X ^ 2) := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P ^ 2 + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * wOf e1 P + X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2)) * hw
    have hg4 : (C g2 : PowerSeries K) = 4 * C (g2 / 4) := by
      rw [← map_ofNat C 4, ← map_mul]
      congr 1
      field_simp
    rw [hg4] at hE
    have he' : 4 * C e1 ^ 3 - 4 * C (g2 / 4) * C e1 - C g3 = (0 : PowerSeries K) := by
      have hc := congrArg (C (R := K)) he
      rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_ofNat, map_zero, hg4] at hc
      linear_combination hc
    rw [show (C (3 * e1) : PowerSeries K) = 3 * C e1 by rw [map_mul, map_ofNat],
      show (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 3 * C e1 ^ 2 - C (g2 / 4) by
        rw [map_sub, map_mul, map_pow, map_ofNat]]
    refine mul_left_cancel₀ (pow_ne_zero 4 (ne_zero_of_constantCoeff hu)) ?_
    linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) - X * (X ^ 3 * dz P - 2)) * hA - 4 * h1 -
      12 * C e1 * h2 - 4 * (3 * C e1 ^ 2 - C (g2 / 4)) * h3 + X ^ 2 * hE + X ^ 8 * he'

end Formalism.L2.Th1.B
