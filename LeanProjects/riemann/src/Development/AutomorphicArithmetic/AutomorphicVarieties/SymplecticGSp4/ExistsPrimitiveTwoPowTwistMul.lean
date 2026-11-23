import Mathlib

theorem UpperTheory.exists_primitive_two_pow_twist_mul :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (c n : ℕ), χ.conductor = 2 ^ c → c < n → ∀ ξ : DirichletCharacter O (2 ^ n), ξ.IsPrimitive → ∃ ξ₁ : DirichletCharacter O (2 ^ n), ξ₁.IsPrimitive ∧ ∀ a : ℤ, IsCoprime a (2 * N : ℕ) → ξ₁ a = χ a * ξ a := by
  intro O _ _ N _ χ c n hc hcn ξ hξ
  obtain ⟨hdN, χ₀, hχ⟩ := DirichletCharacter.factorsThrough_conductor χ
  have hd2 : χ.conductor ∣ 2 ^ n := hc ▸ pow_dvd_pow 2 hcn.le
  set ψ : DirichletCharacter O (2 ^ n) := DirichletCharacter.changeLevel hd2 χ₀ with hψ
  have hn1 : 2 ^ (n - 1) ∣ 2 ^ n := pow_dvd_pow 2 (Nat.sub_le n 1)
  refine ⟨ψ * ξ, ?_, ?_⟩
  · by_contra hnp
    have hψf : ψ.FactorsThrough (2 ^ (n - 1)) :=
      DirichletCharacter.FactorsThrough.mono ψ
        (DirichletCharacter.changeLevel_factorsThrough χ₀ hd2)
        (by rw [hc]; exact pow_dvd_pow 2 (by omega)) hn1
    have hcd := DirichletCharacter.conductor_dvd_level (ψ * ξ)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcd
    have hkn : k ≠ n := by
      intro h
      apply hnp
      rw [DirichletCharacter.isPrimitive_def, hk', h]
    have hpf : (ψ * ξ).FactorsThrough (2 ^ (n - 1)) :=
      DirichletCharacter.FactorsThrough.mono (ψ * ξ)
        (DirichletCharacter.factorsThrough_conductor (ψ * ξ))
        (by rw [hk']; exact pow_dvd_pow 2 (by omega)) hn1
    have hξf : ξ.FactorsThrough (2 ^ (n - 1)) := by
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hn1]
      intro x hx
      have h1 := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hn1).mp hψf hx
      have h2 := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hn1).mp hpf hx
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at h1 h2 ⊢
      rw [MulChar.mul_apply, h1, one_mul] at h2
      exact h2
    have hle : ξ.conductor ≤ 2 ^ (n - 1) := Nat.sInf_le hξf
    have hξ' : ξ.conductor = 2 ^ n := hξ
    rw [hξ'] at hle
    have : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · intro a ha
    have ha' : IsCoprime a (2 * (N : ℤ)) := by exact_mod_cast ha
    have haN : IsCoprime a (N : ℤ) := ha'.of_mul_right_right
    have ha2 : IsCoprime a ((2 ^ n : ℕ) : ℤ) := by
      push_cast
      exact ha'.of_mul_right_left.pow_right
    have e1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hdN haN
    rw [← hχ] at e1
    rw [MulChar.mul_apply, e1, hψ, DirichletCharacter.changeLevel_eq_cast_of_dvd' χ₀ hd2 ha2]
