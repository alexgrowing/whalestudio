import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap :
    ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), IsIntAf (algebraMap ℚ (AfP p) q) → ∃ (r : ℕ) (z : ℤ), (p : ℚ) ^ r * q = z := by
  intro p hp q hq
  have hp' : p.Prime := hp.out
  obtain ⟨r, m, hmp, hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp'.one_lt.ne'
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hden
      exact absurd hden q.den_nz
    · exact h
  have hmc : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp').mpr hmp).symm
  have hint : IsIntAf (algebraMap ℚ (AfP p) q * (p : AfP p) ^ r) := by
    intro v
    rw [map_mul, map_pow, map_natCast]
    exact mul_mem (hq v) (pow_mem (natCast_mem _ p) r)
  have hnum : ((q.num : ℤ) : ℚ) = (m : ℚ) * (q * (p : ℚ) ^ r) := by
    rw [← Rat.mul_den_eq_num]
    have : (q.den : ℚ) = (p : ℚ) ^ r * m := by exact_mod_cast hden
    rw [this]
    ring
  have hdvd : (m : ℤ) ∣ q.num := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p m hm0 hmc q.num _ hint
    rw [hnum, map_mul, map_mul, map_pow, map_natCast, map_natCast]
  have h1 : m ∣ q.num.natAbs := Int.natCast_dvd.mp hdvd
  have h2 : m ∣ q.den := ⟨p ^ r, by rw [hden, mul_comm]⟩
  have hm1 : m = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 q.reduced) h2
  refine ⟨r, q.num, ?_⟩
  rw [← Rat.mul_den_eq_num]
  have : (q.den : ℚ) = (p : ℚ) ^ r := by
    rw [hden, hm1, mul_one]
    push_cast
    rfl
  rw [this, mul_comm]
