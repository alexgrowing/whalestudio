import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.QuadraticExtensions

private lemma sq_in_Zq (q : ℕ) [Fact q.Prime] (d g d0 : ℕ) (hg : 0 < g) (hd : g ^ 2 * d0 = d)
    (h : IsSquare (-(d : ℚ_[q]))) : ∃ z : ℤ_[q], z ^ 2 = -(d0 : ℤ_[q]) := by
  obtain ⟨y, hy⟩ := h
  have hg0 : (g : ℚ_[q]) ≠ 0 := by exact_mod_cast hg.ne'
  have hd' : (d : ℚ_[q]) = (g : ℚ_[q]) ^ 2 * d0 := by rw [← hd]; push_cast; ring
  rw [hd'] at hy
  have hx : (y / g) ^ 2 = -(d0 : ℚ_[q]) := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hg0)]
    linear_combination -hy
  have hxn : ‖y / (g : ℚ_[q])‖ ≤ 1 := by
    have h1 : ‖y / (g : ℚ_[q])‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hx, norm_neg]
      have : ‖((d0 : ℤ_[q]) : ℚ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
      simpa using this
    by_contra hc
    push_neg at hc
    nlinarith
  let z : ℤ_[q] := ⟨y / g, hxn⟩
  have hzc : (z : ℚ_[q]) = y / g := rfl
  refine ⟨z, ?_⟩
  have hc : ((z ^ 2 : ℤ_[q]) : ℚ_[q]) = ((-(d0 : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) := by
    push_cast
    rw [hzc]
    exact hx
  first
    | exact PadicInt.ext hc
    | exact Subtype.ext hc
    | exact PadicInt.coe_injective hc

private lemma not_dvd (q : ℕ) [hq : Fact q.Prime] (d0 : ℕ) (hsq : Squarefree d0) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ¬ q ∣ d0 := by
  intro hdvd
  have hnorm : ‖z‖ ^ 2 = ‖((d0 : ℤ) : ℤ_[q])‖ := by
    rw [← norm_pow, hz, norm_neg, Int.cast_natCast]
  have hd1 : ‖((d0 : ℤ) : ℤ_[q])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (by exact_mod_cast hdvd)
  have hz1 : ‖z‖ < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg z]
  obtain ⟨w, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z).mp hz1
  have hle : ‖((d0 : ℤ) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(2 : ℕ) : ℤ) := by
    rw [← hnorm, norm_mul, PadicInt.norm_p, mul_pow]
    have hw := PadicInt.norm_le_one w
    have he : (q : ℝ) ^ (-(2 : ℕ) : ℤ) = ((q : ℝ)⁻¹) ^ 2 := by
      rw [_root_.zpow_neg, zpow_natCast, inv_pow]
    rw [he]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg w) hw)
  have h2 := PadicInt.norm_int_le_pow_iff_dvd.mp hle
  have h3 : q ^ 2 ∣ d0 := by exact_mod_cast h2
  rw [sq] at h3
  exact (Nat.Prime.one_lt hq.out).ne' (Nat.isUnit_iff.mp (hsq q h3))

private lemma root_mod (q : ℕ) [Fact q.Prime] (d0 : ℕ) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 + d0 := by
  refine ⟨((PadicInt.toZMod z).val : ℤ), ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
  have h := congrArg (PadicInt.toZMod (p := q)) hz
  simp only [map_pow, map_neg, map_natCast] at h
  push_cast
  rw [ZMod.natCast_zmod_val, h]
  ring

private lemma two_case [Fact (Nat.Prime 2)] (d0 : ℕ) (hodd : ¬ 2 ∣ d0) (z : ℤ_[2])
    (hz : z ^ 2 = -(d0 : ℤ_[2])) : d0 % 8 = 7 := by
  have h := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) hz
  rw [map_pow, map_neg, map_natCast] at h
  generalize (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) z = a at h
  revert a
  show ∀ a : ZMod 8, a ^ 2 = -((d0 : ZMod 8)) → d0 % 8 = 7
  rw [← ZMod.natCast_mod d0 8]
  have hlt := Nat.mod_lt d0 (by norm_num : 8 > 0)
  have hodd : d0 % 2 = 1 := by omega
  interval_cases h8 : d0 % 8
  all_goals first | omega | decide

private lemma not_dvd_four (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : ¬ (q : ℤ) ∣ 4 := by
  intro h
  have h' : q ∣ 2 ^ 2 := by exact_mod_cast h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h'))

private lemma root_odd (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (d0 m : ℕ) (hm : d0 + 1 = 4 * m) (r0 : ℤ)
    (hr : (q : ℤ) ∣ r0 ^ 2 + d0) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - 1 * r + m := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q + 1 = 2 * k := by
    rcases hq.eq_two_or_odd' with h | ⟨j, hj⟩
    · exact absurd h h2
    · exact ⟨j + 1, by omega⟩
  refine ⟨(r0 + 1) * k, ?_⟩
  have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have h4 : (q : ℤ) ∣ 4 * (((r0 + 1) * k) ^ 2 - 1 * ((r0 + 1) * k) + m) := by
    obtain ⟨c, hc⟩ := hr
    have hk' : (2 * k : ℤ) = q + 1 := by exact_mod_cast hk.symm
    have hm' : (4 * m : ℤ) = d0 + 1 := by exact_mod_cast hm.symm
    refine ⟨c + (r0 + 1) * (2 * r0 + (r0 + 1) * q), ?_⟩
    linear_combination ((r0 + 1) ^ 2 * (2 * (k : ℤ) + q + 1) - 2 * (r0 + 1)) * hk' + hm' + hc
  rcases hpz.dvd_or_dvd h4 with h | h
  · exact absurd h (not_dvd_four q hq h2)
  · exact h

end UpperTheory.Gal.W2.Seed.QuadraticExtensions

open UpperTheory.Gal.W2.Seed.QuadraticExtensions in
theorem UpperTheory.Gal.W2.Seed.pQuadEx :
    QuadEx := by
  intro d hd
  obtain ⟨d0, g, hgd, hsq⟩ := Nat.sq_mul_squarefree d
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hd0 : 0 < d0 := by
    rcases Nat.eq_zero_or_pos d0 with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdq : (d : ℚ) = (g : ℚ) ^ 2 * d0 := by rw [← hgd]; push_cast; ring
  by_cases h43 : d0 % 4 = 3
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, d0 + 1 = 4 * m := ⟨(d0 + 1) / 4, by omega⟩
    have hdisc : (1 : ℤ) ^ 2 - 4 * (m : ℤ) = -(d0 : ℤ) := by
      have : ((d0 : ℤ) + 1) = 4 * (m : ℤ) := by exact_mod_cast hm
      linarith
    refine ⟨1, m, 1 / (g : ℚ), ?_, ?_, ?_⟩
    · rw [hdisc]; omega
    · rw [hdisc, hdq]; push_cast; field_simp
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · rw [hdisc, dvd_neg]
        intro h
        exact hnd (by exact_mod_cast h)
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          refine ⟨0, ?_⟩
          have : (m : ℤ) % 2 = 0 := by omega
          push_cast
          omega
        · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
          exact root_odd q (Fact.out) hq2 d0 m hm r0 hr0
  · refine ⟨0, d0, 2 / (g : ℚ), ?_, ?_, ?_⟩
    · omega
    · rw [hdq]; push_cast; field_simp; ring
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          omega
        · have hq : q.Prime := Fact.out
          have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
          intro h
          have h' : (q : ℤ) ∣ 4 * (d0 : ℤ) := by
            have : (0 : ℤ) ^ 2 - 4 * (d0 : ℤ) = -(4 * (d0 : ℤ)) := by ring
            rw [this, dvd_neg] at h
            exact h
          rcases hpz.dvd_or_dvd h' with h4 | h4
          · exact not_dvd_four q hq hq2 h4
          · exact hnd (by exact_mod_cast h4)
      · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
        exact ⟨r0, by simpa using hr0⟩
