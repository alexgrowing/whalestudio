import Mathlib

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.logDerivativeThreeFourOne

lemma comb_nonneg {z : ℂ} (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have e := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at e
    nlinarith
  have e2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by simp [sq]
  rw [e2]
  nlinarith [sq_nonneg (z.re + 1)]

lemma neg_logDeriv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ))) s n).re)
      (-(deriv (LFunction χ) s / LFunction χ s).re) := by
  have h := (LSeriesSummable_twist_vonMangoldt χ hs).LSeriesHasSum
  rw [LSeries_twist_vonMangoldt_eq χ hs, ← deriv_LFunction_eq_deriv_LSeries χ hs,
    ← LFunction_eq_LSeries χ hs] at h
  have h' := Complex.hasSum_re h
  simpa [neg_div] using h'

lemma term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term ((fun n : ℕ => (1 : DirichletCharacter ℂ q) n) *
          (fun n : ℕ => (vonMangoldt n : ℂ))) σ n).re
      + 4 * (LSeries.term ((fun n : ℕ => χ n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + t * I) n).re
      + (LSeries.term ((fun n : ℕ => (χ ^ 2) n) * (fun n : ℕ => (vonMangoldt n : ℂ)))
          (σ + 2 * t * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hA : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) σ
  set A : ℝ := (n : ℝ) ^ σ with hAdef
  have hA0 : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  set b : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hbdef
  have ha : (n : ℂ) ^ (σ : ℂ) = (A : ℂ) := by
    rw [hAdef, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_cast
  have hb : ‖b‖ = 1 := by
    rw [hbdef, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hb0 : b ≠ 0 := by
    rintro h
    simp [h] at hb
  have e1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = A * b := by
    rw [cpow_add _ _ hn', ha]
  have e2 : (n : ℂ) ^ ((σ : ℂ) + 2 * t * I) = A * b ^ 2 := by
    rw [cpow_add _ _ hn', ha, hbdef, ← cpow_nat_mul]
    push_cast
    ring_nf
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  rw [e1, e2, ha]
  set c : ℝ := vonMangoldt n / A with hcdef
  have hc : 0 ≤ c := div_nonneg vonMangoldt_nonneg hA.le
  by_cases hu : IsUnit (n : ZMod q)
  · have hz : ‖χ n / b‖ = 1 := by
      rw [norm_div, hb, div_one]
      simpa using χ.unit_norm_eq_one hu.unit
    have k1 : (1 : DirichletCharacter ℂ q) n * (vonMangoldt n : ℂ) / (A : ℂ) = (c : ℂ) := by
      rw [MulChar.one_apply hu, one_mul, hcdef, Complex.ofReal_div]
    have k2 : χ n * (vonMangoldt n : ℂ) / ((A : ℂ) * b) = (c : ℂ) * (χ n / b) := by
      rw [hcdef, Complex.ofReal_div]
      field_simp
    have k3 : (χ ^ 2) n * (vonMangoldt n : ℂ) / ((A : ℂ) * b ^ 2) = (c : ℂ) * (χ n / b) ^ 2 := by
      rw [MulChar.pow_apply' χ two_ne_zero, hcdef, Complex.ofReal_div]
      field_simp
    rw [k1, k2, k3, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hcomb := comb_nonneg hz
    nlinarith [mul_nonneg hc hcomb]
  · simp [MulChar.map_nonunit _ hu]

theorem three_four_one : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ), 1 < σ → 0 ≤ -(3 * (deriv (LFunction (1 : DirichletCharacter ℂ q)) σ / LFunction (1 : DirichletCharacter ℂ q) σ).re + 4 * (deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re + (deriv (LFunction (χ ^ 2)) (σ + 2 * t * I) / LFunction (χ ^ 2) (σ + 2 * t * I)).re) := by
  intro q _ χ σ t hσ
  have h1 := neg_logDeriv_eq (1 : DirichletCharacter ℂ q) (s := (σ : ℂ)) (by simpa using hσ)
  have h2 := neg_logDeriv_eq χ (s := (σ : ℂ) + t * I) (by simpa using hσ)
  have h3 := neg_logDeriv_eq (χ ^ 2) (s := (σ : ℂ) + 2 * t * I) (by simpa using hσ)
  have h := ((h1.mul_left 3).add (h2.mul_left 4)).add h3
  have hnn := h.nonneg (fun n => term_nonneg χ σ t n)
  linarith

end GlobalTheory.logDerivativeThreeFourOne
