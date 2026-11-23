import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

private theorem padic_val_one_add_mul_pow_pow_sub_one (l : ℕ) (hl : l.Prime) (f : ℕ) (hf : f.Coprime l) (j : ℕ) :
    (l : ℤ) ^ (ee l + j) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 ∧
      ¬ (l : ℤ) ^ (ee l + j + 1) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hfl : ¬ (l : ℤ) ∣ (f : ℤ) := by
    intro hd
    have hd' : l ∣ f := Int.natCast_dvd_natCast.mp hd
    exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hf.symm hd')
  have hq : emultiplicity (l : ℤ) ((f : ℤ) * (l : ℤ) ^ ee l) = (ee l : ℕ∞) := by
    rw [emultiplicity_mul hp, emultiplicity_pow_self_of_prime hp, emultiplicity_eq_zero.mpr hfl,
      zero_add]
  have hx : ¬ (l : ℤ) ∣ 1 + (f : ℤ) * (l : ℤ) ^ ee l := by
    intro hd
    have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
    have h2 : (l : ℤ) ∣ (f : ℤ) * (l : ℤ) ^ ee l :=
      Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
    have h3 : (l : ℤ) ∣ 1 := by
      have := dvd_sub hd h2
      simpa using this
    have h4 : l ∣ 1 := by exact_mod_cast h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h4)
  have key : emultiplicity (l : ℤ) ((1 + (f : ℤ) * (l : ℤ) ^ ee l) ^ l ^ j - 1)
      = ((ee l + j : ℕ) : ℕ∞) := by
    by_cases h2 : l = 2
    · subst h2
      have e2 : ee 2 = 2 := by simp [ee]
      have h4 : (4 : ℤ) ∣ (1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) - 1 := by
        rw [e2]
        exact ⟨f, by push_cast; ring⟩
      have hx2 : ¬ (2 : ℤ) ∣ 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2 := by
        simpa using hx
      have := Int.two_pow_two_pow_sub_pow_two_pow (x := 1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2)
        (y := 1) j h4 hx2
      rw [one_pow, add_sub_cancel_left] at this
      have hq2 : emultiplicity (2 : ℤ) ((f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) = (ee 2 : ℕ∞) := by
        simpa using hq
      rw [hq2] at this
      have : emultiplicity ((2 : ℕ) : ℤ) ((1 + (f : ℤ) * ((2 : ℕ) : ℤ) ^ ee 2) ^ 2 ^ j - 1)
          = (ee 2 : ℕ∞) + j := by simpa using this
      rw [this]
      push_cast
      rfl
    · have hodd : Odd l := hl.odd_of_ne_two h2
      have e1 : ee l = 1 := by simp [ee, h2]
      have hxy : (l : ℤ) ∣ (1 + (f : ℤ) * (l : ℤ) ^ ee l) - 1 := by
        rw [add_sub_cancel_left]
        exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _
      have := Int.emultiplicity_pow_sub_pow hl hodd hxy hx (l ^ j)
      rw [one_pow, add_sub_cancel_left, hq,
        emultiplicity_pow_self_of_prime (Nat.prime_iff.mp hl) j] at this
      rw [this]
      push_cast
      rfl
  constructor
  · rw [pow_dvd_iff_le_emultiplicity, key]
  · rw [pow_dvd_iff_le_emultiplicity, key]
    norm_cast
    omega

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.FW.gamGen :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (γ : (ZMod (f * l ^ n))ˣ), f.Coprime l → ee l ≤ n → (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l → (ZMod.unitsMap h).ker = Subgroup.zpowers γ ∧ γ ^ l ^ n = 1 := by
  intro l _ f n h γ hf hen hγ
  have hl : l.Prime := Fact.out
  obtain ⟨d, rfl⟩ : ∃ d, n = ee l + d := ⟨n - ee l, by omega⟩
  have he : 1 ≤ ee l := by unfold ee; split_ifs <;> norm_num
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : l = 1 := by simpa [Nat.Coprime] using hf
    exact hl.one_lt.ne' this
  haveI : NeZero (f * l ^ (ee l + d)) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (f * l ^ ee l) := ⟨Nat.mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  set x : ℤ := 1 + (f : ℤ) * (l : ℤ) ^ ee l with hxdef
  have hγx : (γ : ZMod (f * l ^ (ee l + d))) = ((x : ℤ) : ZMod (f * l ^ (ee l + d))) := by
    rw [hγ, hxdef]
    push_cast
    ring
  have hcop : IsCoprime (f : ℤ) ((l : ℤ) ^ (ee l + d)) := by
    rw [← Int.natCast_pow, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ hf
  have hpow : ∀ m : ℕ, γ ^ m = 1 ↔ (l : ℤ) ^ (ee l + d) ∣ x ^ m - 1 := by
    intro m
    have hfdvd : (f : ℤ) ∣ x ^ m - 1 := by
      have h1 : x - 1 ∣ x ^ m - 1 ^ m := sub_dvd_pow_sub_pow x 1 m
      rw [one_pow] at h1
      refine dvd_trans ?_ h1
      rw [hxdef, add_sub_cancel_left]
      exact dvd_mul_right _ _
    rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, hγx, ← Int.cast_pow,
      ← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    constructor
    · intro hd
      exact dvd_trans (dvd_mul_left _ _) hd
    · intro hd
      exact hcop.mul_dvd hfdvd hd
  have hord : orderOf γ = l ^ d := by
    rcases d with _ | d
    · rw [pow_zero, orderOf_eq_one_iff]
      have h1 : γ ^ (l ^ 0) = 1 := by
        rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf 0).1
      simpa using h1
    · apply orderOf_eq_prime_pow
      · rw [hpow, hxdef, ← Nat.add_assoc]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf d).2
      · rw [hpow, hxdef]
        exact (padic_val_one_add_mul_pow_pow_sub_one l hl f hf (d + 1)).1
  set K := (ZMod.unitsMap h).ker with hK
  have c1 : Nat.card (ZMod (f * l ^ (ee l + d)))ˣ = (f * l ^ (ee l + d)).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have c2 : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcardK : Nat.card K = l ^ d := by
    have a := Subgroup.card_mul_index K
    rw [hK, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective h),
      Subgroup.card_top, c1, c2,
      Nat.totient_mul (Nat.Coprime.pow_right _ hf), Nat.totient_mul (Nat.Coprime.pow_right _ hf),
      Nat.totient_prime_pow hl (by omega), Nat.totient_prime_pow hl (by omega)] at a
    have hpos : 0 < f.totient * (l ^ (ee l - 1) * (l - 1)) := by
      have h1 := hl.one_lt
      have h2 := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hf0)
      exact Nat.mul_pos h2 (Nat.mul_pos (pow_pos hl.pos _) (by omega))
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hK, a]
    have : ee l + d - 1 = (ee l - 1) + d := by omega
    rw [this, pow_add]
    ring
  have hmem : γ ∈ K := by
    rw [hK, MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, Units.val_one,
      MonoidHom.coe_coe, hγ, map_add, map_one, map_mul, map_pow, map_natCast, map_natCast]
    have h0 : ((f * l ^ ee l : ℕ) : ZMod (f * l ^ ee l)) = 0 := ZMod.natCast_self _
    push_cast at h0
    rw [h0, add_zero]
  have hle : Subgroup.zpowers γ ≤ K := (Subgroup.zpowers_le).mpr hmem
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle ?_).symm, ?_⟩
  · rw [Nat.card_zpowers, hord, hcardK]
  · rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact pow_dvd_pow l (by omega)
