import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsIntHigherStickelbergerDenomSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detprod
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chcard
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.NormCharEvalHigherStickelbergerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.GroupRingCharEvalStickelbergerYNeZeroOfParity

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.higherStickelberger_det_exists_int_bounded :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] [Finite Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ a → 2 ≤ k → π (-1) ≠ 1 → ∃ X : ℤ, X ≠ 0 ∧ X.natAbs ≤ bdX N a k ^ (Nat.card Γ / 2) ∧ (X : ℚ) = (denY N k : ℚ) ^ (Nat.card Γ / 2) * detR (π (-1)) ((-1) ^ k) (yEl k a ha π) := by
  intro N _ Γ _ _ π a ha k h2a hk hc
  have hN : 2 ≤ N := by
    by_contra h
    have h0 := NeZero.ne N
    obtain rfl : N = 1 := by omega
    exact hc (by rw [Subsingleton.elim (-1 : (ZMod 1)ˣ) 1, map_one])
  have hcc : π (-1) * π (-1) = 1 := by rw [← map_mul]; simp
  have hε : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  haveI : NeZero (Monoid.exponent Γ : ℂ) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨z, hz⟩ := exists_int_higherStickelbergerDenom_smul π a ha k (by omega)
  have hX : ((detR (π (-1)) ((-1) ^ k) z : ℤ) : ℚ) =
      (denY N k : ℚ) ^ (Nat.card Γ / 2) * detR (π (-1)) ((-1) ^ k) (yEl k a ha π) := by
    rw [← detR_coefMap, hz, detR_smul, card_Qc' hcc hc]
  have hp := det_mul_quotientByOrderTwo_eq_prod_charEval (A := ℚ) (Ω := ℂ) (π (-1)) ((-1) ^ k) hcc hc hε (yEl k a ha π)
  have hD : (0 : ℚ) < denY N k := by exact_mod_cast denY_pos (by omega) (by omega)
  refine ⟨_, ?_, ?_, hX⟩
  · have : algebraMap ℚ ℂ (detR (π (-1)) ((-1) ^ k) (yEl k a ha π)) ≠ 0 := by
      rw [hp]
      exact Finset.prod_ne_zero_iff.2 fun χ _ => groupRingCharEval_stickelbergerY_ne_zero_of_parity π χ.1 a ha k hN h2a hk (by simpa using χ.2)
    intro h
    rw [h, Int.cast_zero, eq_comm, mul_eq_zero] at hX
    rcases hX with h | h
    · exact (pow_pos hD _).ne' h
    · exact this (by rw [h, map_zero])
  · have h1 : ‖algebraMap ℚ ℂ (detR (π (-1)) ((-1) ^ k) (yEl k a ha π))‖ ≤ (sizeY N a k : ℝ) ^ (Nat.card Γ / 2) := by
      rw [hp, norm_prod, ← card_Qc' hcc hc, ← card_signedInvolutionChar_eq_card_involutionQuotient (Ω := ℂ) _ _ hcc hc hε, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun χ _ => norm_charEval_higherStickelberger_le π χ.1 a ha k hN (by omega)
    have h2 : (((detR (π (-1)) ((-1) ^ k) z).natAbs : ℕ) : ℝ) = ‖algebraMap ℚ ℂ ((detR (π (-1)) ((-1) ^ k) z : ℤ) : ℚ)‖ := by
      rw [map_intCast, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
    have h3 : (((detR (π (-1)) ((-1) ^ k) z).natAbs : ℕ) : ℝ) ≤ ((bdX N a k ^ (Nat.card Γ / 2) : ℕ) : ℝ) := by
      rw [h2, hX, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast, bdX]
      push_cast
      rw [mul_pow]
      gcongr
    exact_mod_cast h3
