import Formalism.PeriodIntegrals.WOnLatG

namespace PI.UnitaryGroupMassFormula.WOnLatG

open PI.WPhDefs

theorem exp_pi_int (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  have h : (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem neg_one_zpow_odd_mul {n : ℤ} (hn : Odd n) (m : ℤ) : (-1 : ℂ) ^ (n * m) = (-1 : ℂ) ^ m := by
  rw [zpow_mul, hn.neg_one_zpow]

theorem main : PI.WOnLatG := by
  intro T I J _ _ _ s A La' hLa p hp x hx
  obtain ⟨m, hm⟩ := (hLa x hx).1
  have hal : alG s A x = (-1 : ℂ) ^ m := by
    have : s * (HfG A x x).re = (m : ℝ) := hm
    simp only [alG, this, round_intCast]
  rw [hal]
  unfold wPhG
  split_ifs with h2
  · rw [hm]; exact exp_pi_int m
  · have hne : ∃ c : ℂ, ∃ (k : ℕ) (m' : ℤ), (p : ℝ) ^ k * qG s A x = (m' : ℝ) ∧ c = (-1 : ℂ) ^ m' :=
      ⟨(-1 : ℂ) ^ m, 0, m, by rw [hm]; simp, rfl⟩
    obtain ⟨k, m', hk, hc⟩ := Classical.epsilon_spec hne
    rw [hc]
    rw [hm] at hk
    have hm' : m' = (p : ℤ) ^ k * m := by
      have : ((m' : ℤ) : ℝ) = (((p : ℤ) ^ k * m : ℤ) : ℝ) := by rw [← hk]; push_cast; ring
      exact_mod_cast this
    have hodd : Odd ((p : ℤ) ^ k) := by
      have : Odd p := hp.odd_of_ne_two h2
      exact (Int.odd_coe_nat p |>.2 this).pow
    rw [hm', neg_one_zpow_odd_mul hodd]

end PI.UnitaryGroupMassFormula.WOnLatG
