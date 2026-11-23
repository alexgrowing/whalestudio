import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chitheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BLprim
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primlevel

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerY_eq_euler_mul_genBernoulli :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ N → ev ℚ χ (yEl k a ha π) = (1 - (a : Ω) ^ k * dirOf π χ (a : ZMod N)) * (-genB k (dirOf π χ) / k) := by
  intro Ω _ _ N _ Γ _ π χ a ha k hN
  rw [yEl, map_mul, map_sub, map_one, ev_single, groupRingCharEval_stickelbergerTheta_eq_neg_genBernoulli π χ k hN, ← dirOf_unit, ZMod.coe_unitOfCoprime]
  simp

theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerY_ne_zero_of_parity :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* ℂˣ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ N → 2 ≤ a → 2 ≤ k → ((χ (π (-1)) : ℂˣ) : ℂ) = (-1) ^ k → ev ℚ χ (yEl k a ha π) ≠ 0 := by
  intro N _ Γ _ π χ a ha k hN h2a hk hs
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpar : dirOf π χ (-1) = (-1) ^ k := by
    have := dirOf_unit π χ (-1)
    rw [map_inv, Units.val_inv_eq_inv_val, hs, Units.val_neg, Units.val_one] at this
    rw [this, ← inv_pow, inv_neg, inv_one]
  rw [groupRingCharEval_stickelbergerY_eq_euler_mul_genBernoulli π χ a ha k hN]
  refine mul_ne_zero (fun h => ?_) (div_ne_zero (neg_ne_zero.2 ((b_nzC _ k (by omega) hpar).2 hk)) hk0)
  have h1 : ‖dirOf π χ (a : ZMod N)‖ = 1 := by
    rw [← ZMod.coe_unitOfCoprime a ha]; exact DirichletCharacter.unit_norm_eq_one _ _
  have h2 := congrArg norm (sub_eq_zero.1 h)
  rw [norm_one, norm_mul, h1, norm_pow, Complex.norm_natCast, mul_one] at h2
  have h3 : 1 < a ^ k := Nat.one_lt_pow (by omega) (by omega)
  exact h3.ne (by exact_mod_cast h2)
