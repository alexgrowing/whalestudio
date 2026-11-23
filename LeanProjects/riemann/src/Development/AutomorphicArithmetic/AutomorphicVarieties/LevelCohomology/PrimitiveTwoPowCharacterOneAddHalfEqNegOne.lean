import Mathlib

theorem UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), 2 ≤ n → ∀ ξ : DirichletCharacter R (2 ^ n), ξ.IsPrimitive → ξ (1 + 2 ^ (n - 1)) = -1 := by
  intro R _ _ n hn ξ hξ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk]
  have h2 : (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = 0 := by
    have := ZMod.natCast_self (2 ^ (k + 2))
    push_cast at this
    exact this
  have huu : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1)) = 1 := by
    have e : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1))
        = 1 + 2 ^ (k + 2) * (1 + 2 ^ k) := by ring
    rw [e, h2, zero_mul, add_zero]
  have hsq : ξ (1 + 2 ^ (k + 1)) * ξ (1 + 2 ^ (k + 1)) = 1 := by
    rw [← map_mul, huu, map_one]
  have hpm : ξ (1 + 2 ^ (k + 1)) = 1 ∨ ξ (1 + 2 ^ (k + 1)) = -1 := by
    have : (ξ (1 + 2 ^ (k + 1)) - 1) * (ξ (1 + 2 ^ (k + 1)) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with h1 | h1
  · exfalso
    have hd : 2 ^ (k + 1) ∣ 2 ^ (k + 2) := pow_dvd_pow 2 (by omega)
    have hft : ξ.FactorsThrough (2 ^ (k + 1)) := by
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      intro x hx
      have hx' := hx
      rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
        Units.val_one] at hx'
      have hx'' : (((x : ZMod (2 ^ (k + 2))).val : ℕ) : ZMod (2 ^ (k + 1))) = ((1 : ℕ) : ZMod _) := by
        rw [hx', Nat.cast_one]
      rw [ZMod.natCast_eq_natCast_iff] at hx''
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      have hv : (x : ZMod (2 ^ (k + 2))).val < 2 ^ (k + 2) := ZMod.val_lt _
      have hM : 2 ≤ 2 ^ (k + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmod : (x : ZMod (2 ^ (k + 2))).val % 2 ^ (k + 1) = 1 := by
        have h := hx''
        unfold Nat.ModEq at h
        rw [h]
        exact Nat.mod_eq_of_lt (by omega)
      have hq : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        calc (x : ZMod (2 ^ (k + 2))).val < 2 ^ (k + 2) := hv
          _ = 2 * 2 ^ (k + 1) := by ring
      have hdm := Nat.div_add_mod (x : ZMod (2 ^ (k + 2))).val (2 ^ (k + 1))
      rw [← ZMod.natCast_zmod_val (x : ZMod (2 ^ (k + 2)))]
      generalize hqd : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) = q at hq hdm
      rcases (by omega : q = 0 ∨ q = 1) with hq0 | hq1
      · rw [hq0, mul_zero, zero_add, hmod] at hdm
        rw [← hdm, Nat.cast_one, map_one]
      · rw [hq1, mul_one, hmod] at hdm
        rw [← hdm]
        push_cast
        rw [add_comm ((2 : ZMod (2 ^ (k + 2))) ^ (k + 1)) 1]
        exact h1
    have hle : ξ.conductor ≤ 2 ^ (k + 1) :=
      Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff _).mpr hft)
    have hlt : 2 ^ (k + 1) < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [DirichletCharacter.isPrimitive_def] at hξ
    omega
  · exact h1
