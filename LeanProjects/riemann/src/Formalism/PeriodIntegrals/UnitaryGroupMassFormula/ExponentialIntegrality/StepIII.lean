import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatCastMemWittIntegers

noncomputable section

namespace PI.ExpIntWProof

open PI

theorem div_pow_mem (h : KeyW) (p : ℕ) [hp : Fact p.Prime] :
    ∀ k : ℕ, ∀ y : ℂ_[p], y ∈ Wp p → ‖y‖ ≤ ((p : ℝ)⁻¹) ^ k → y / (p : ℂ_[p]) ^ k ∈ Wp p := by
  intro k
  induction k with
  | zero => intro y hy _; simpa using hy
  | succ k ih =>
    intro y hy hnorm
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hlt : ‖y‖ < 1 :=
      lt_of_le_of_lt hnorm (pow_lt_one₀ hpos.le hpinv (Nat.succ_ne_zero k))
    have h1 : y / (p : ℂ_[p]) ∈ PI.Wp p := h p y hy hlt
    have h2 : ‖y / (p : ℂ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ k := by
      rw [norm_div, norm_p, div_le_iff₀ hpos, ← pow_succ]
      exact hnorm
    have h3 := ih _ h1 h2
    rwa [div_div, ← pow_succ'] at h3

theorem stepIII_of_key (h : KeyW) : StepIII := by
  intro p hp x hx hnorm
  obtain ⟨k, hk⟩ := hx
  have hp0 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hn : ‖(p : ℂ_[p]) ^ k * x‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [norm_mul, norm_pow, norm_p]
    exact mul_le_of_le_one_right (by positivity) hnorm
  have h3 := div_pow_mem h p k _ hk hn
  rwa [mul_div_cancel_left₀ _ (pow_ne_zero k hp0)] at h3

theorem expIntW_of_key (h1 : StepI) (h : KeyW) : ExpIntW :=
  expIntW_of_steps h1 (stepIII_of_key h)

end PI.ExpIntWProof

end
