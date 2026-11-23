import Mathlib

namespace DualFramesAlt.Val

open scoped BigOperators

section SlopeTestRemainingChoices

variable {p : ℕ} [hp : Fact p.Prime]

private theorem prime_prime_padicInt : Prime (p : ℤ_[p]) := PadicInt.irreducible_p.prime

private theorem not_prime_dvd_padicInt_unit (w : ℤ_[p]ˣ) : ¬ (p : ℤ_[p]) ∣ (w : ℤ_[p]) :=
  fun h => prime_prime_padicInt.not_unit (isUnit_of_dvd_unit h (Units.isUnit _))

lemma emult_eq_valuation {x : ℤ_[p]} (hx : x ≠ 0) :
    emultiplicity (p : ℤ_[p]) x = x.valuation := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [emultiplicity_mul hP, emultiplicity_eq_zero.mpr (not_prime_dvd_padicInt_unit _), zero_add,
    emultiplicity_pow_self_of_prime hP]

lemma valuation_eq_of_emult {x : ℤ_[p]} {n : ℕ} (h : emultiplicity (p : ℤ_[p]) x = n) :
    x.valuation = n := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp at h
  rw [emult_eq_valuation hx] at h
  exact_mod_cast h

lemma emult_of_valuation_one {x : ℤ_[p]} (hx : x ≠ 0) (h1 : x.valuation = 1) :
    emultiplicity (p : ℤ_[p]) x = 1 := by
  rw [emult_eq_valuation hx, h1, Nat.cast_one]

lemma p_dvd_of_valuation_one {x : ℤ_[p]} (hx : x ≠ 0) (h1 : x.valuation = 1) :
    (p : ℤ_[p]) ∣ x := by
  have h := emult_of_valuation_one hx h1
  by_contra hn
  rw [emultiplicity_eq_zero.mpr hn] at h
  exact zero_ne_one h

lemma not_dvd_of_dvd_sub_one {u : ℤ_[p]} (h : (p : ℤ_[p]) ∣ u - 1) : ¬ (p : ℤ_[p]) ∣ u := by
  intro hu
  have h1 : (p : ℤ_[p]) ∣ 1 := by simpa using dvd_sub hu h
  exact prime_prime_padicInt.not_unit (isUnit_of_dvd_one h1)

lemma dvd_of_natCast_dvd_natCast {m : ℕ} (h : (p : ℤ_[p]) ∣ (m : ℤ_[p])) : p ∣ m := by
  have h1 := (PadicInt.norm_lt_one_iff_dvd _).mpr h
  have h2 : ‖((m : ℤ) : ℤ_[p])‖ < 1 := by simpa using h1
  exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h2)

lemma emult_pow_sub_one (hodd : p ≠ 2) {u : ℤ_[p]} (hdvd : (p : ℤ_[p]) ∣ u - 1)
    (he : emultiplicity (p : ℤ_[p]) (u - 1) = 1) {k : ℕ} (hk : k ≠ 0) :
    emultiplicity (p : ℤ_[p]) (u ^ k - 1) = ((1 + padicValNat p k : ℕ) : ℕ∞) := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  have hp1 : Odd p := hp.out.odd_of_ne_two hodd
  have hu : ¬ (p : ℤ_[p]) ∣ u := not_dvd_of_dvd_sub_one hdvd
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.out.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have hval : padicValNat p (p ^ e * m) = e := by
    rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have h1 : emultiplicity (p : ℤ_[p]) (u ^ p ^ e - 1 ^ p ^ e) = 1 + e := by
    rw [emultiplicity_pow_prime_pow_sub_pow_prime_pow hP hp1 hdvd hu e, he]
  rw [one_pow] at h1
  have hx : ¬ (p : ℤ_[p]) ∣ u ^ p ^ e := fun h => hu (hP.dvd_of_dvd_pow h)
  have hxy : (p : ℤ_[p]) ∣ u ^ p ^ e - 1 := by
    have h2 := sub_dvd_pow_sub_pow u 1 (p ^ e)
    rw [one_pow] at h2
    exact hdvd.trans h2
  have hmR : ¬ (p : ℤ_[p]) ∣ (m : ℤ_[p]) := fun h => hm (dvd_of_natCast_dvd_natCast h)
  have key : emultiplicity (p : ℤ_[p]) ((u ^ p ^ e) ^ m - 1 ^ m)
      = emultiplicity (p : ℤ_[p]) (u ^ p ^ e - 1) :=
    emultiplicity_pow_sub_pow_of_prime hP hxy hx hmR
  rw [one_pow, ← pow_mul] at key
  rw [key, h1, hval]
  norm_cast

lemma emult_zpow_sub_one (hodd : p ≠ 2) (u : ℤ_[p]ˣ) (hdvd : (p : ℤ_[p]) ∣ (u : ℤ_[p]) - 1)
    (he : emultiplicity (p : ℤ_[p]) ((u : ℤ_[p]) - 1) = 1) {i : ℤ} (hi : i ≠ 0) :
    emultiplicity (p : ℤ_[p]) (((u ^ i : ℤ_[p]ˣ) : ℤ_[p]) - 1)
      = ((1 + padicValNat p i.natAbs : ℕ) : ℕ∞) := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg i
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hi (by simp)
    have hab : ((n : ℤ)).natAbs = n := by simp
    rw [hab, zpow_natCast, Units.val_pow_eq_pow_val]
    exact emult_pow_sub_one hodd hdvd he hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hi (by simp)
    have hab : (-(n : ℤ)).natAbs = n := by simp
    have h1 : (((u ^ n)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
    have hrw : (((u ^ (-(n : ℤ))) : ℤ_[p]ˣ) : ℤ_[p]) - 1
        = (((u ^ n)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * -((u : ℤ_[p]) ^ n - 1) := by
      rw [zpow_neg, zpow_natCast]
      linear_combination h1
    rw [hab, hrw, emultiplicity_mul hP, emultiplicity_eq_zero.mpr (not_prime_dvd_padicInt_unit _), zero_add,
      emultiplicity_neg]
    exact emult_pow_sub_one hodd hdvd he hn

end SlopeTestRemainingChoices

theorem val_prod_one_sub_zpow {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2)
    (u : ℤ_[p]ˣ) (hu1 : ((u : ℤ_[p]) - 1).valuation = 1) (hu0 : (u : ℤ_[p]) - 1 ≠ 0)
    (Ω : Finset ℤ) (h0 : (0 : ℤ) ∉ Ω) :
    (∏ i ∈ Ω, (1 - ((u ^ i : ℤ_[p]ˣ) : ℤ_[p]))).valuation
      = ∑ i ∈ Ω, (1 + padicValNat p i.natAbs) := by
  have hP : Prime (p : ℤ_[p]) := prime_prime_padicInt
  have hdvd := p_dvd_of_valuation_one hu0 hu1
  have he := emult_of_valuation_one hu0 hu1
  have key : ∀ i ∈ Ω, emultiplicity (p : ℤ_[p]) (1 - ((u ^ i : ℤ_[p]ˣ) : ℤ_[p]))
      = ((1 + padicValNat p i.natAbs : ℕ) : ℕ∞) := by
    intro i hi
    rw [← neg_sub, emultiplicity_neg]
    exact emult_zpow_sub_one hodd u hdvd he (fun h => h0 (h ▸ hi))
  apply valuation_eq_of_emult
  rw [Finset.emultiplicity_prod hP, Finset.sum_congr rfl key, Nat.cast_sum]

end DualFramesAlt.Val
