import Formalism.WindowSums.Statement

namespace Formalism.WindowSums

open Finset

section ZpowValAux

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

lemma zv_prime : Prime (ℓ : ℤ_[ℓ]) := PadicInt.prime_p

lemma zv_emult_eq_val {x : ℤ_[ℓ]} (hx : x ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) x = (x.valuation : ℕ∞) := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit (Units.isUnit _),
    zero_add, emultiplicity_pow_self_of_prime zv_prime]

lemma zv_emult_unit_mul {c : ℤ_[ℓ]} (hc : IsUnit c) (y : ℤ_[ℓ]) :
    emultiplicity (ℓ : ℤ_[ℓ]) (c * y) = emultiplicity (ℓ : ℤ_[ℓ]) y := by
  rw [emultiplicity_mul zv_prime, emultiplicity_of_isUnit_right zv_prime.not_unit hc, zero_add]

lemma zv_not_dvd_of_dvd_sub_one {x : ℤ_[ℓ]} (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1) : ¬ (ℓ : ℤ_[ℓ]) ∣ x := by
  intro h
  have h1 : (ℓ : ℤ_[ℓ]) ∣ 1 := by
    have h2 := dvd_sub h hx
    rwa [sub_sub_cancel] at h2
  exact zv_prime.not_unit (isUnit_of_dvd_one h1)

lemma zv_two_sq_step (h2 : ℓ = 2) {x : ℤ_[ℓ]} (h4 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ 2 - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + 1 := by
  have hx1 : (ℓ : ℤ_[ℓ]) ∣ x - 1 := (dvd_pow_self _ two_ne_zero).trans h4
  have e : x + 1 = (x - 1) + (ℓ : ℤ_[ℓ]) := by
    have hc : (ℓ : ℤ_[ℓ]) = 2 := by
      have h7 := congrArg (fun n : ℕ => (n : ℤ_[ℓ])) h2
      simpa using h7
    rw [hc]
    ring

  have hp1 : emultiplicity (ℓ : ℤ_[ℓ]) (x + 1) = 1 := by
    rw [← Nat.cast_one (R := ℕ∞), emultiplicity_eq_coe]
    refine ⟨by rw [pow_one, e]; exact dvd_add hx1 dvd_rfl, fun hd => ?_⟩
    have h3 : (ℓ : ℤ_[ℓ]) ^ 2 ∣ (ℓ : ℤ_[ℓ]) ^ 1 := by
      have h5 := dvd_sub hd h4
      rw [e, add_sub_cancel_left] at h5
      rw [pow_one]
      exact h5
    have h6 := (pow_dvd_pow_iff zv_prime.ne_zero zv_prime.not_unit).1 h3
    omega
  rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring, emultiplicity_mul zv_prime, hp1]

lemma zv_pow_prime_pow (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) (k : ℕ) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ ℓ ^ k - 1) = emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + k := by
  by_cases hl : ℓ = 2
  · have h4 := h2 hl
    induction k with
    | zero => simp
    | succ k ih =>
      have hy : (ℓ : ℤ_[ℓ]) ^ 2 ∣ x ^ ℓ ^ k - 1 := h4.trans (sub_one_dvd_pow_sub_one x _)
      have e : x ^ ℓ ^ (k + 1) = (x ^ ℓ ^ k) ^ 2 := by
        rw [pow_succ, pow_mul]
        exact congrArg (fun n => (x ^ ℓ ^ k) ^ n) hl
      rw [e, zv_two_sq_step hl hy, ih]
      push_cast
      ring
  · have hodd : Odd ℓ := hℓ.out.odd_of_ne_two hl
    have h1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow (x := x) (y := 1) zv_prime hodd
      (by simpa using hx) (zv_not_dvd_of_dvd_sub_one hx) k
    rwa [one_pow] at h1

lemma zv_not_dvd_cast {m : ℕ} (hm : ¬ ℓ ∣ m) : ¬ (ℓ : ℤ_[ℓ]) ∣ (m : ℤ_[ℓ]) := by
  intro h
  rw [← PadicInt.norm_lt_one_iff_dvd] at h
  have h' : ‖((m : ℤ) : ℤ_[ℓ])‖ < 1 := by
    rw [Int.cast_natCast]
    exact h
  exact hm (Int.natCast_dvd_natCast.1 ((PadicInt.norm_int_lt_one_iff_dvd (m : ℤ)).1 h'))

lemma zv_pow_nat (x : ℤ_[ℓ]) (hx : (ℓ : ℤ_[ℓ]) ∣ x - 1)
    (h2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ x - 1) {n : ℕ} (hn : n ≠ 0) :
    emultiplicity (ℓ : ℤ_[ℓ]) (x ^ n - 1) =
      emultiplicity (ℓ : ℤ_[ℓ]) (x - 1) + padicValNat ℓ n := by
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ hℓ.out.ne_one
  have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
  have hy1 : (ℓ : ℤ_[ℓ]) ∣ x ^ ℓ ^ e - 1 := hx.trans (sub_one_dvd_pow_sub_one x _)
  have h1 := emultiplicity_pow_sub_pow_of_prime zv_prime hy1
    (zv_not_dvd_of_dvd_sub_one (by simpa using hy1)) (zv_not_dvd_cast hm)
  rw [one_pow] at h1
  have hv : padicValNat ℓ (ℓ ^ e * m) = e := by
    rw [padicValNat.mul (pow_ne_zero _ hℓ.out.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  rw [pow_mul, h1, zv_pow_prime_pow x hx h2 e, hv]

end ZpowValAux

theorem valuation_zpow_sub_one : ZpowVal := by
  intro ℓ _ u s hs1 hs2 hval j hj

  have key : ∀ y : ℤ_[ℓ]ˣ, emultiplicity (ℓ : ℤ_[ℓ]) ((y : ℤ_[ℓ]) - 1) = s → ∀ n : ℕ, n ≠ 0 →
      ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 ∧
        PadicInt.valuation (((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s + padicValNat ℓ n := by
    intro y hy n hn
    have hy1 : (ℓ : ℤ_[ℓ]) ∣ (y : ℤ_[ℓ]) - 1 := by
      have h1 := pow_dvd_of_le_emultiplicity (k := 1) (by rw [hy]; exact_mod_cast hs1)
      rwa [pow_one] at h1
    have hy2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ (y : ℤ_[ℓ]) - 1 := fun h =>
      pow_dvd_of_le_emultiplicity (by rw [hy]; exact_mod_cast hs2 h)
    have he := zv_pow_nat (y : ℤ_[ℓ]) hy1 hy2 hn
    rw [← Units.val_pow_eq_pow_val, hy] at he
    have hne : ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 := by
      intro h0
      rw [h0, emultiplicity_zero] at he
      exact absurd he (by norm_cast)
    refine ⟨hne, ?_⟩
    rw [zv_emult_eq_val hne] at he
    exact_mod_cast he
  have hx0 : (u : ℤ_[ℓ]) - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hval
    omega
  have hem : emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) - 1) = s := by
    rw [zv_emult_eq_val hx0, hval]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj rfl
    rw [zpow_natCast, padicValInt.of_nat]
    exact key u hem n hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj (by simp)
    have hinv : emultiplicity (ℓ : ℤ_[ℓ]) (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s := by
      have e : ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 = (-((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) * ((u : ℤ_[ℓ]) - 1) := by
        rw [mul_sub, neg_mul, Units.inv_mul]
        ring
      rw [e, zv_emult_unit_mul (Units.isUnit _).neg, hem]
    have hv : padicValInt ℓ (-(n : ℤ)) = padicValNat ℓ n := by
      simp [padicValInt]
    rw [zpow_neg, zpow_natCast, ← inv_pow, hv]
    exact key u⁻¹ hinv n hn

end Formalism.WindowSums
