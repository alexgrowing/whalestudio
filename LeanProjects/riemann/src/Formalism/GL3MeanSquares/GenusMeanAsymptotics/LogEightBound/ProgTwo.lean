import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffFinal

noncomputable section

namespace Formalism.HermitianLattices.Ext.B4

theorem log_eight_mul_le {M : ℕ} (hM : 3 ≤ M) : Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) ≤ 3 * Real.log M := by
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h8 : 2 * (M : ℝ) * ((2 : ℕ) + 2) = 8 * M := by push_cast; ring
  have h3 : 3 * Real.log M = Real.log ((M : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
  rw [h8, h3]
  apply Real.log_le_log (by positivity)
  have h9 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have : (M : ℝ) ^ 3 = (M : ℝ) * (M : ℝ) ^ 2 := by ring
  rw [this]; nlinarith

theorem progTwo : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 3 ≤ M → ∃ p p' : ℕ, p ≠ p' ∧ p.Prime ∧ p'.Prime ∧
    p ≡ 1 [MOD M] ∧ p' ≡ 1 [MOD M] ∧ Real.log p ≤ C * Real.log M ^ 2 ∧ Real.log p' ≤ C * Real.log M ^ 2 := by
  obtain ⟨C, hC, h⟩ := Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesEff
  refine ⟨9 * C, by positivity, fun M hM => ?_⟩
  obtain ⟨S, hS, hq⟩ := h M 2 (by omega)
  obtain ⟨p, p', hne, rfl⟩ := Finset.card_eq_two.1 hS
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog0 : 0 ≤ Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) := by
    apply Real.log_nonneg; push_cast; nlinarith
  have hle := log_eight_mul_le hM
  have hsq : Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) ^ 2 ≤ 9 * Real.log M ^ 2 := by nlinarith
  have key : ∀ q ∈ ({p, p'} : Finset ℕ), Real.log q ≤ 9 * C * Real.log M ^ 2 := by
    intro q hqS
    obtain ⟨hqp, -, hqle⟩ := hq q hqS
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have h1 : Real.log q ≤ C * Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) ^ 2 := by
      have := Real.log_le_log hq0 hqle
      rwa [Real.log_exp] at this
    nlinarith
  have hp := hq p (by simp)
  have hp' := hq p' (by simp)
  exact ⟨p, p', hne, hp.1, hp'.1, hp.2.1, hp'.2.1, key p (by simp), key p' (by simp)⟩

end Formalism.HermitianLattices.Ext.B4

end
