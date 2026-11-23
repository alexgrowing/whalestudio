import Mathlib

private theorem UpperTheory.hasEnoughRootsOfUnity_exponent_units_zmod_two_pow (O : Type) [CommRing O] (k j : ℕ) (hj : j ≤ k + 3)
    [HasEnoughRootsOfUnity O (2 ^ (k + 3))] :
    HasEnoughRootsOfUnity O (Monoid.exponent (ZMod (2 ^ j))ˣ) := by
  have hd : Monoid.exponent (ZMod (2 ^ j))ˣ ∣ 2 ^ (k + 3) := by
    refine Group.exponent_dvd_card.trans ?_
    rw [ZMod.card_units_eq_totient]
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h
      simp
    · rw [Nat.totient_prime_pow Nat.prime_two h]
      simpa using pow_dvd_pow 2 (by omega : j - 1 ≤ k + 3)
  exact HasEnoughRootsOfUnity.of_dvd O hd

theorem UpperTheory.exists_primitive_odd_dirichletCharacter_two_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] (n : ℕ), 3 ≤ n → HasEnoughRootsOfUnity O (2 ^ n) → ∃ ξ : DirichletCharacter O (2 ^ n), ξ.IsPrimitive ∧ ξ (-1) = -1 := by
  intro O _ _ n hn hroots
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e1 := UpperTheory.hasEnoughRootsOfUnity_exponent_units_zmod_two_pow O k (k + 3) le_rfl
  have e2 := UpperTheory.hasEnoughRootsOfUnity_exponent_units_zmod_two_pow O k 2 (by omega)
  set z : ℤ := 1 + 2 ^ (k + 2) with hz
  have hcopN : IsCoprime z ((2 ^ (k + 3) : ℕ) : ℤ) := by
    refine ⟨1 - 2 ^ (k + 2), 2 ^ (k + 1), ?_⟩
    push_cast
    rw [hz]
    ring
  have hzN : ((z : ℤ) : ZMod (2 ^ (k + 3))) ≠ 1 := by
    rw [hz]
    push_cast
    intro h
    have h0 : ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 3))) = 0 := by
      push_cast
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by positivity) h0
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : k + 2 < k + 3)
    omega
  have hz4 : ((z : ℤ) : ZMod (2 ^ 2)) = 1 := by
    rw [hz]
    push_cast
    rw [pow_add, show (2 : ZMod (2 ^ 2)) ^ 2 = 0 from by decide, mul_zero, add_zero]
  have hzM : ((z : ℤ) : ZMod (2 ^ (k + 2))) = 1 := by
    rw [hz]
    push_cast
    rw [show (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) by
      push_cast; rfl, ZMod.natCast_self, add_zero]
  have prim : ∀ χ : DirichletCharacter O (2 ^ (k + 3)), χ (z : ZMod (2 ^ (k + 3))) ≠ 1 →
      χ.IsPrimitive := by
    intro χ hχ
    rw [DirichletCharacter.isPrimitive_def]
    obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 χ.conductor_dvd_level
    by_contra hne
    have hik : i ≤ k + 2 := by
      rcases Nat.lt_or_ge i (k + 3) with h | h
      · omega
      · exact absurd (by rw [hc, show i = k + 3 by omega]) hne
    have hf0 : χ.FactorsThrough (2 ^ i) := by
      rw [← hc]
      exact χ.factorsThrough_conductor
    have hf : χ.FactorsThrough (2 ^ (k + 2)) :=
      DirichletCharacter.FactorsThrough.mono _ hf0 (pow_dvd_pow 2 hik) (pow_dvd_pow 2 (by omega))
    apply hχ
    rw [hf.eq_changeLevel, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hf.dvd hcopN, hzM,
      map_one]
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity O hzN
  obtain ⟨ψ₀, hψ₀⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity O
    (show (-1 : ZMod (2 ^ 2)) ≠ 1 by decide)
  have h42 : 2 ^ 2 ∣ 2 ^ (k + 3) := pow_dvd_pow 2 (by omega)
  set ψ := DirichletCharacter.changeLevel h42 ψ₀ with hψ
  have hcm1 : IsCoprime (-1 : ℤ) ((2 ^ (k + 3) : ℕ) : ℤ) := isCoprime_one_left.neg_left
  have hψz : ψ (z : ZMod (2 ^ (k + 3))) = 1 := by
    rw [hψ, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ h42 hcopN, hz4, map_one]
  have hψm : ψ (-1) = -1 := by
    have h1 : ψ (-1) = ψ₀ (-1) := by
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ₀ h42 hcm1
      push_cast at this
      rw [hψ, this]
    rw [h1]
    have hsq : ψ₀ (-1) * ψ₀ (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    rcases mul_self_eq_one_iff.1 hsq with h | h
    · exact absurd h hψ₀
    · exact h
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rcases mul_self_eq_one_iff.1 hsq with h | h
  · refine ⟨χ * ψ, prim _ ?_, ?_⟩
    · rw [MulChar.mul_apply, hψz, mul_one]
      exact hχ
    · rw [MulChar.mul_apply, h, hψm, one_mul]
  · exact ⟨χ, prim χ hχ, h⟩
