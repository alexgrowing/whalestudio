import Mathlib

namespace GlobalTheory.RationalIntegralCoordinates

theorem exists_coords {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) {z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ)) :
    ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * r := by
  have hint : IsIntegral ℚ r := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [hr]
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hzK
  induction hzK using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap q => exact ⟨q, 0, by simp [eq_ratCast]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination (b : ℂ) * e * hr

theorem conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : r.re = 0 := by
    by_contra hne
    have him : r.im = 0 := by
      have hprod : r.re * r.im = 0 := by linarith
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h hne
      · exact h
    rw [him] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [hre]

theorem rat_int {q : ℚ} (h : IsIntegral ℤ (q : ℂ)) : ∃ m : ℤ, (m : ℚ) = q := by
  have hq : IsIntegral ℤ q := by
    have hinj : Function.Injective (algebraMap ℚ ℂ).toIntAlgHom := (algebraMap ℚ ℂ).injective
    rw [← isIntegral_algHom_iff _ hinj]
    simpa [eq_ratCast] using h
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  exact ⟨m, by simpa using hm⟩

theorem int_of_prime_mul_sq {d : ℕ} (hd : d.Prime) {q : ℚ} {n : ℤ}
    (h : (d : ℚ) * q ^ 2 = n) : ∃ k : ℤ, (k : ℚ) = q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hz : (d : ℤ) * q.num ^ 2 = (q.den : ℤ) ^ 2 * n := by
    have hq : q = q.num / q.den := (Rat.num_div_den q).symm
    rw [hq, div_pow] at h
    field_simp at h
    exact_mod_cast h
  have hcop : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  have hdvd : (q.den : ℤ) ^ 2 ∣ d := hcop.dvd_of_dvd_mul_right ⟨n, hz⟩
  have hdvd' : q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    exact (dvd_pow_self _ two_ne_zero).trans this
  rcases hd.eq_one_or_self_of_dvd _ hdvd' with h1 | h1
  · exact ⟨q.num, by rw [← Rat.den_eq_one_iff]; exact h1⟩
  · exfalso
    have h2 : q.den ^ 2 ∣ d := by exact_mod_cast hdvd
    rw [h1] at h2
    have h3 := Nat.le_of_dvd hd.pos h2
    have h4 := hd.two_le
    nlinarith

theorem main {d : ℕ} (hd : Nat.Prime d) (hd4 : d % 4 = 3) {r : ℂ} (hr : r ^ 2 = -(d : ℂ))
    (T : Subring ℂ) (hT : (1 + r) / 2 ∈ T) {z : ℂ}
    (hzK : z ∈ IntermediateField.adjoin ℚ ({r} : Set ℂ)) (hz : IsIntegral ℤ z) : z ∈ T := by
  have hd0 : 0 < d := hd.pos
  obtain ⟨a, b, rfl⟩ := exists_coords hd0 hr hzK
  have hc : starRingEnd ℂ ((a : ℂ) + b * r) = a - b * r := by
    rw [map_add, map_mul, conj_eq_neg hd0 hr, map_ratCast, map_ratCast]
    ring
  have hcz : IsIntegral ℤ (starRingEnd ℂ ((a : ℂ) + b * r)) := hz.map (starRingEnd ℂ).toIntAlgHom
  have htr : IsIntegral ℤ (((2 * a : ℚ)) : ℂ) := by
    have e : (((2 * a : ℚ)) : ℂ) = ((a : ℂ) + b * r) + starRingEnd ℂ ((a : ℂ) + b * r) := by
      rw [hc]
      push_cast
      ring
    rw [e]
    exact hz.add hcz
  have hnm : IsIntegral ℤ (((a ^ 2 + d * b ^ 2 : ℚ)) : ℂ) := by
    have e : (((a ^ 2 + d * b ^ 2 : ℚ)) : ℂ) =
        ((a : ℂ) + b * r) * starRingEnd ℂ ((a : ℂ) + b * r) := by
      rw [hc]
      push_cast
      linear_combination (b : ℂ) ^ 2 * hr
    rw [e]
    exact hz.mul hcz
  obtain ⟨m, hm⟩ := rat_int htr
  obtain ⟨N, hN⟩ := rat_int hnm
  obtain ⟨k, hk⟩ := int_of_prime_mul_sq hd (q := 2 * b) (n := 4 * N - m ^ 2) (by
    push_cast
    rw [hm, hN]
    ring)
  have heq : m ^ 2 + (d : ℤ) * k ^ 2 = 4 * N := by
    have : ((m ^ 2 + (d : ℤ) * k ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [hm, hk, hN]
      ring
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) = 4 * t + 3 := ⟨(d / 4 : ℕ), by omega⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m - k = 2 * j := by
    obtain ⟨u, hu | hu⟩ := Int.even_or_odd' m <;> obtain ⟨v, hv | hv⟩ := Int.even_or_odd' k
    · exact ⟨u - v, by omega⟩
    · exfalso
      obtain ⟨X, hX⟩ : ∃ X : ℤ, (d : ℤ) = 4 * X :=
        ⟨N - u ^ 2 - d * (v ^ 2 + v), by rw [hu, hv] at heq; linear_combination heq⟩
      omega
    · exfalso
      obtain ⟨X, hX⟩ : ∃ X : ℤ, (1 : ℤ) = 4 * X :=
        ⟨N - u ^ 2 - u - d * v ^ 2, by rw [hu, hv] at heq; linear_combination heq⟩
      omega
    · exact ⟨u - v, by omega⟩
  have hm' : (m : ℂ) = 2 * a := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) hm
  have hk' : (k : ℂ) = 2 * b := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) hk
  have hj' : (m : ℂ) - k = 2 * j := by exact_mod_cast hj
  have hsplit : (a : ℂ) + b * r = (j : ℂ) + (k : ℂ) * ((1 + r) / 2) := by
    linear_combination (-1 / 2 : ℂ) * hm' + (-r / 2) * hk' + (1 / 2 : ℂ) * hj'
  rw [hsplit]
  exact T.add_mem (intCast_mem T j) (T.mul_mem (intCast_mem T k) hT)

end GlobalTheory.RationalIntegralCoordinates
