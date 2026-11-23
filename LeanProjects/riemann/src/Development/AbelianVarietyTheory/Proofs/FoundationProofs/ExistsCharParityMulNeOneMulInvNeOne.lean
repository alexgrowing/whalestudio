import Mathlib

namespace GlobalTheory

theorem exists_char_parity_mul_ne_one_mul_inv_ne_one : ∀ (N r : ℕ) (χ : DirichletCharacter ℂ N) (sg : ℂ), 0 < N → r.Prime → 7 ≤ r → r ∣ N → (sg = 1 ∨ sg = -1) → ∃ θ : DirichletCharacter ℂ N, θ (-1) = sg ∧ θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1 := by
  intro N r χ sg hN hr hr7 hrN hsg
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero r := ⟨hr.ne_zero⟩
  have hrle : r ≤ N := Nat.le_of_dvd hN hrN

  haveI : Fact (2 < N) := ⟨by omega⟩
  have hm1 : (-1 : ZMod N) ≠ 1 := ZMod.neg_one_ne_one
  obtain ⟨θ₁, hθ₁⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hm1
  have hsq : ∀ ψ : DirichletCharacter ℂ N, ψ (-1) * ψ (-1) = 1 := by
    intro ψ
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hθ₁' : θ₁ (-1) = -1 := by
    rcases mul_self_eq_one_iff.mp (hsq θ₁) with h | h
    · exact absurd h hθ₁
    · exact h

  have h16 : (16 : ZMod r) ≠ 1 := by
    intro h
    have h15 : ((15 : ℕ) : ZMod r) = 0 := by
      have : (16 : ZMod r) - 1 = 0 := by rw [h]; ring
      have e : ((15 : ℕ) : ZMod r) = (16 : ZMod r) - 1 := by push_cast; ring
      rw [e, this]
    rw [ZMod.natCast_eq_zero_iff] at h15
    have h35 : r ∣ 3 * 5 := by norm_num; exact h15
    rcases (Nat.Prime.dvd_mul hr).mp h35 with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3; omega
    · have := Nat.le_of_dvd (by norm_num) h5; omega
  obtain ⟨κ, hκ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h16
  set ψ : DirichletCharacter ℂ N := DirichletCharacter.changeLevel hrN κ with hψ
  have hη4 : ψ ^ 4 ≠ 1 := by
    intro h
    have h' : DirichletCharacter.changeLevel hrN (κ ^ 4) = DirichletCharacter.changeLevel hrN 1 := by
      rw [map_pow, map_one]; exact h
    have hk := DirichletCharacter.changeLevel_injective hrN h'
    apply hκ
    have : (κ ^ 4) 2 = (1 : DirichletCharacter ℂ r) 2 := by rw [hk]
    have hu : IsUnit (2 : ZMod r) := by
      have : (2 : ZMod r) = ((2 : ℕ) : ZMod r) := by norm_cast
      rw [this, ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_primes Nat.prime_two hr).mpr (by omega)
    rw [MulChar.one_apply hu, MulChar.pow_apply' _ (by norm_num)] at this
    have e : (16 : ZMod r) = 2 ^ 4 := by norm_num
    rw [e, map_pow]; exact this
  set η : DirichletCharacter ℂ N := ψ ^ 2 with hηdef
  have hηsq : η ^ 2 ≠ 1 := by
    rw [hηdef, ← pow_mul]; exact hη4
  have hη1 : η ≠ 1 := by
    intro h; apply hηsq; rw [h, one_pow]
  have hη2 : η (-1) = 1 := by
    rw [hηdef, pow_two, MulChar.mul_apply, hsq]
  have hη2' : (η ^ 2) (-1) = 1 := by
    rw [pow_two, MulChar.mul_apply, hη2, mul_one]

  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : DirichletCharacter ℂ N, θ₀ (-1) = sg := by
    rcases hsg with h | h
    · exact ⟨1, by rw [h]; exact MulChar.one_apply (isUnit_one.neg)⟩
    · exact ⟨θ₁, by rw [h, hθ₁']⟩

  have hab : θ₀ ≠ θ₀ * η := by
    intro h; apply hη1; exact left_eq_mul.mp h
  have hbc : θ₀ * η ≠ θ₀ * η ^ 2 := by
    intro h; apply hη1
    have h' := mul_left_cancel h
    rw [pow_two] at h'
    exact left_eq_mul.mp h'
  have hac : θ₀ ≠ θ₀ * η ^ 2 := by
    intro h; apply hηsq; exact left_eq_mul.mp h
  have key : ∀ θ : DirichletCharacter ℂ N, ¬ (θ * χ ≠ 1 ∧ θ * χ⁻¹ ≠ 1) → θ = χ⁻¹ ∨ θ = χ := by
    intro θ h
    by_cases h1 : θ * χ = 1
    · exact Or.inl (eq_inv_of_mul_eq_one_left h1)
    · have h2 : θ * χ⁻¹ = 1 := by
        by_contra h2; exact h ⟨h1, h2⟩
      right
      have := eq_inv_of_mul_eq_one_left h2
      rwa [inv_inv] at this
  by_contra hno
  push_neg at hno
  have ha := key θ₀ (fun h => by have := hno θ₀ hθ₀ h.1; exact h.2 this)
  have hb := key (θ₀ * η) (fun h => by
    have := hno (θ₀ * η) (by rw [MulChar.mul_apply, hθ₀, hη2, mul_one]) h.1; exact h.2 this)
  have hc := key (θ₀ * η ^ 2) (fun h => by
    have := hno (θ₀ * η ^ 2) (by rw [MulChar.mul_apply, hθ₀, hη2', mul_one]) h.1; exact h.2 this)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    first
    | exact hab (ha.trans hb.symm)
    | exact hac (ha.trans hc.symm)
    | exact hbc (hb.trans hc.symm)

end GlobalTheory
