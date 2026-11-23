import Mathlib

private theorem primitive_dyadic_character_ne_one (R : Type) [CommRing R] (m : ℕ)
    (ξ : DirichletCharacter R (2 ^ (m + 2))) (hξ : ξ.IsPrimitive) :
    ξ (1 + 2 ^ (m + 1)) ≠ 1 := by
  intro h
  have hd : 2 ^ (m + 1) ∣ 2 ^ (m + 2) := pow_dvd_pow 2 (by omega)
  have hf : ξ.FactorsThrough (2 ^ (m + 1)) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).2 fun x hx => ?_
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one,
      ZMod.cast_eq_val] at hx
    have hM : 1 < 2 ^ (m + 1) := Nat.one_lt_two_pow (by omega)
    have hx1 : ((x : ZMod (2 ^ (m + 2))).val : ZMod (2 ^ (m + 1))) = ((1 : ℕ) : ZMod (2 ^ (m + 1))) := by
      simpa using hx
    have hx2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hx1
    rw [Nat.mod_eq_of_lt hM] at hx2
    have hlt := ZMod.val_lt (x : ZMod (2 ^ (m + 2)))
    have h2 : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by ring
    have hq : (x : ZMod (2 ^ (m + 2))).val / 2 ^ (m + 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      omega
    have hv := Nat.mod_add_div (x : ZMod (2 ^ (m + 2))).val (2 ^ (m + 1))
    rw [hx2] at hv
    have hx' : (x : ZMod (2 ^ (m + 2))) =
        ((1 + 2 ^ (m + 1) * ((x : ZMod (2 ^ (m + 2))).val / 2 ^ (m + 1)) : ℕ) :
          ZMod (2 ^ (m + 2))) := by
      rw [hv, ZMod.natCast_zmod_val]
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, hx']
    interval_cases hq' : (x : ZMod (2 ^ (m + 2))).val / 2 ^ (m + 1)
    · simp
    · push_cast
      simpa using h
  have hle : ξ.conductor ≤ 2 ^ (m + 1) := Nat.sInf_le hf
  rw [hξ] at hle
  have h2 : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by ring
  have : 0 < 2 ^ (m + 1) := by positivity
  omega

private theorem two_adic_unit_pow_two_pow (x k : ℕ) (j : ℕ) (hx : ∃ d, x = 1 + 2 ^ (k + 2) * (2 * d + 1)) :
    ∃ d, x ^ (2 ^ j) = 1 + 2 ^ (k + 2 + j) * (2 * d + 1) := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + 2 ^ (k + j) * (2 * d + 1) ^ 2, ?_⟩
    rw [pow_succ 2 j, pow_mul, hd]
    ring

private theorem two_adic_unit_pow_odd (x k : ℕ) (w : ℕ) (hx : ∃ d, x = 1 + 2 ^ (k + 1) * (2 * d + 1)) :
    ∃ d, x ^ (2 * w + 1) = 1 + 2 ^ (k + 1) * (2 * d + 1) := by
  obtain ⟨c, hc⟩ := hx
  induction w with
  | zero => exact ⟨c, by simpa using hc⟩
  | succ w ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + ((2 * c + 1) + 2 ^ k * (2 * c + 1) ^ 2) * (1 + 2 ^ (k + 1) * (2 * d + 1)), ?_⟩
    have : x ^ (2 * (w + 1) + 1) = x ^ (2 * w + 1) * x ^ 2 := by ring
    rw [this, hd, hc]
    ring

theorem UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (ξ : DirichletCharacter O (2 ^ n)), ξ.IsPrimitive → ∀ v a u : ℕ, Odd v → 1 < v → Odd u → ξ (v : ZMod (2 ^ n)) ^ (2 ^ a * u) = 1 → 2 ^ n < v ^ 2 * 2 ^ a := by
  intro O _ _ n ξ hξ v a u hv hv1 hu h
  obtain ⟨t, ht⟩ := hv
  obtain ⟨u', hu'⟩ := hu
  have hv3 : 3 ≤ v := by omega
  have hpos : 0 < 2 ^ a := by positivity
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h1 : 2 ^ n ≤ 2 := by interval_cases n <;> norm_num
    have h2 : 9 ≤ v ^ 2 := by nlinarith
    nlinarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hsq : v ^ 2 = 4 * (t * (t + 1)) + 1 := by rw [ht]; ring
  have hw : v ^ 2 - 1 ≠ 0 := by
    rw [hsq, Nat.add_sub_cancel]
    have : 0 < t := by omega
    positivity
  obtain ⟨s, r, hr, hsr⟩ := Nat.exists_eq_two_pow_mul_odd hw
  have hs : 2 ≤ s := by
    by_contra hs
    obtain ⟨e, he⟩ := hr
    rw [hsq, Nat.add_sub_cancel] at hsr
    generalize t * (t + 1) = P at hsr
    interval_cases s <;> omega
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  obtain ⟨d, rfl⟩ := hr
  have hW : v ^ 2 = 1 + 2 ^ (k + 1 + 1) * (2 * d + 1) := by
    have := Nat.eq_add_of_sub_eq (by omega) hsr
    rw [this]
    ring
  obtain ⟨d1, hd1⟩ := two_adic_unit_pow_odd (v ^ 2) (k + 1) u' ⟨d, hW⟩
  obtain ⟨d2, hd2⟩ := two_adic_unit_pow_two_pow ((v ^ 2) ^ (2 * u' + 1)) k a ⟨d1, by rw [hd1]⟩
  have hbig : m + 2 ≤ k + 2 + a := by
    by_contra hlt
    obtain ⟨d3, hd3⟩ := two_adic_unit_pow_two_pow (((v ^ 2) ^ (2 * u' + 1)) ^ 2 ^ a) (k + a) (m + 1 - (k + 2 + a))
      ⟨d2, by rw [hd2, show k + 2 + a = k + a + 2 by ring]⟩
    rw [show k + a + 2 + (m + 1 - (k + 2 + a)) = m + 1 by omega] at hd3
    apply primitive_dyadic_character_ne_one O m ξ hξ
    have hcast : ((((((v ^ 2) ^ (2 * u' + 1)) ^ 2 ^ a) ^ 2 ^ (m + 1 - (k + 2 + a)) : ℕ)) :
        ZMod (2 ^ (m + 2))) = 1 + 2 ^ (m + 1) := by
      rw [hd3]
      push_cast
      have h0 : (2 : ZMod (2 ^ (m + 2))) ^ (m + 2) = 0 := by
        rw [show (2 : ZMod (2 ^ (m + 2))) ^ (m + 2) = ((2 ^ (m + 2) : ℕ) : ZMod (2 ^ (m + 2))) by
          push_cast; rfl, ZMod.natCast_self]
      linear_combination (d3 : ZMod (2 ^ (m + 2))) * h0
    rw [← hcast]
    have hval : ((((((v ^ 2) ^ (2 * u' + 1)) ^ 2 ^ a) ^ 2 ^ (m + 1 - (k + 2 + a)) : ℕ)) :
        ZMod (2 ^ (m + 2))) = ((v : ZMod (2 ^ (m + 2))) ^ (2 ^ a * u)) ^ (2 * 2 ^ (m + 1 - (k + 2 + a))) := by
      rw [hu']
      push_cast
      ring
    rw [hval, map_pow, map_pow, h, one_pow]
  have hk : 2 ^ (k + 2) < v ^ 2 := by
    rw [hW]
    have : 2 ^ (k + 2) ≤ 2 ^ (k + 1 + 1) * (2 * d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  calc 2 ^ (m + 2) ≤ 2 ^ (k + 2 + a) := Nat.pow_le_pow_right (by norm_num) hbig
    _ = 2 ^ (k + 2) * 2 ^ a := by ring
    _ < v ^ 2 * 2 ^ a := Nat.mul_lt_mul_of_pos_right hk hpos
