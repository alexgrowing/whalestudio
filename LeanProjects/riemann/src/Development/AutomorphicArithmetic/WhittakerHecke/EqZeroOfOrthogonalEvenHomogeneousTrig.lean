import Mathlib

open Complex MeasureTheory

private lemma UpperTheory.fourier_vanishing_homogeneous (F : ℝ → ℂ) (hc : Continuous F) (hp : ∀ t, F (t + Real.pi) = F t)
    (h : ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) →
      ∫ t in (0 : ℝ)..2 * Real.pi,
        MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p * F t = 0)
    (s : ℂ) (hs : s = 1 ∨ s = -1) (k : ℕ) :
    ∫ t in (0 : ℝ)..2 * Real.pi, cexp (s * (2 * k) * (t * I)) * F t = 0 := by
  have hhom : ((MvPolynomial.X 1 + MvPolynomial.C (s * I) * MvPolynomial.X 0 :
      MvPolynomial (Fin 2) ℂ) ^ (2 * k)).IsHomogeneous (2 * k) := by
    have h1 : (MvPolynomial.X 1 + MvPolynomial.C (s * I) * MvPolynomial.X 0 :
        MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X ℂ 1).add (MvPolynomial.isHomogeneous_C_mul_X _ _)
    simpa using h1.pow (2 * k)
  have := h k _ hhom
  rw [← this]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have he : cexp (s * (t * I)) = (Real.cos t : ℂ) + s * I * (Real.sin t : ℂ) := by
    rcases hs with rfl | rfl
    · rw [one_mul, exp_mul_I]; push_cast; ring
    · have : (-1 : ℂ) * (t * I) = ((-t : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg]
      push_cast; ring
  have hpow : cexp (s * (2 * k) * (t * I)) = cexp (s * (t * I)) ^ (2 * k) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  simp only [map_pow, map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [hpow, he]

theorem UpperTheory.eq_zero_of_orthogonal_even_homogeneous_trig :
    ∀ (F : ℝ → ℂ), Continuous F → (∀ t, F (t + Real.pi) = F t) →
        (∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) →
          ∫ t in (0 : ℝ)..2 * Real.pi, MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p * F t = 0) →
        ∀ t, F t = 0 := by
  intro F hc hp h
  haveI : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩
  have hper : Function.Periodic F Real.pi := hp
  let f : C(AddCircle Real.pi, ℂ) :=
    ⟨hper.lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hc⟩
  have hfx : ∀ x : ℝ, f (x : AddCircle Real.pi) = F x := fun x => hper.lift_coe x

  have hint : ∀ n : ℤ, ∫ t in (0 : ℝ)..Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t = 0 := by
    intro n
    have hG : Function.Periodic (fun t : ℝ => cexp ((-(2 * n : ℂ)) * (t * I)) * F t) Real.pi := by
      intro t
      have h1 : cexp ((-(2 * n : ℂ)) * (((t + Real.pi : ℝ) : ℂ) * I)) =
          cexp ((-(2 * n : ℂ)) * (t * I)) := by
        have : (-(2 * n : ℂ)) * (((t + Real.pi : ℝ) : ℂ) * I) =
            (-(2 * n : ℂ)) * (t * I) + ((-n : ℤ) : ℂ) * (2 * Real.pi * I) := by
          push_cast; ring
        rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
      simp only [h1, hp]
    have hcont : Continuous (fun t : ℝ => cexp ((-(2 * n : ℂ)) * (t * I)) * F t) := by
      fun_prop
    have hsplit : ∫ t in (0 : ℝ)..2 * Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t =
        2 * ∫ t in (0 : ℝ)..Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 Real.pi) (hcont.intervalIntegrable Real.pi (2 * Real.pi))]
      have := hG.intervalIntegral_add_eq Real.pi 0
      rw [show Real.pi + Real.pi = 2 * Real.pi by ring, zero_add] at this
      rw [this]; ring
    have hz : ∫ t in (0 : ℝ)..2 * Real.pi, cexp ((-(2 * n : ℂ)) * (t * I)) * F t = 0 := by
      rcases le_total 0 n with hn | hn
      · have := UpperTheory.fourier_vanishing_homogeneous F hc hp h (-1) (Or.inr rfl) n.toNat
        have e : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hn)
        rw [e] at this
        rw [← this]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [neg_mul, one_mul]
      · have := UpperTheory.fourier_vanishing_homogeneous F hc hp h 1 (Or.inl rfl) (-n).toNat
        have e : (((-n).toNat : ℕ) : ℂ) = -(n : ℂ) := by
          have h2 : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (neg_nonneg.2 hn)
          rw [← Int.cast_natCast, h2, Int.cast_neg]
        rw [e] at this
        rw [← this]
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [one_mul, mul_neg]
    rw [hz] at hsplit
    exact (mul_eq_zero.1 hsplit.symm).resolve_left two_ne_zero
  have hF : ∀ n : ℤ, fourierCoeff f n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have e : ∀ x : ℝ, fourier (-n) (x : AddCircle Real.pi) • f (x : AddCircle Real.pi) =
        cexp ((-(2 * n : ℂ)) * (x * I)) * F x := by
      intro x
      have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
      rw [fourier_coe_apply, smul_eq_mul, hfx]
      congr 2
      push_cast
      field_simp
    simp only [e]
    rw [hint n, smul_zero]
  have hsum : Summable (fourierCoeff f) := by
    rw [show fourierCoeff f = 0 from funext hF]
    exact summable_zero
  intro t
  have hs := has_pointwise_sum_fourier_series_of_summable hsum (t : AddCircle Real.pi)
  simp only [hF, zero_smul] at hs
  rw [← hfx]
  exact hs.unique hasSum_zero
