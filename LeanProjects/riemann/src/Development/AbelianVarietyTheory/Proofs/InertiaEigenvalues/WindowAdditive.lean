import Mathlib

namespace GlobalTheory.PMonE

theorem window_additive (q : ℝ) (hq : 2 ≤ q) (r : ℤ) (α f : ℤ → ℝ) (hα : Antitone α)
    (hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * (q ^ (r - J) - 1)) :
    (∀ J, J ≤ r → f J + α J ≤ f r + α r) ∧
    (∀ J, r + 1 ≤ J → f J - α J / 2 ≤ f r - α (r + 1) / 2) := by
  have hd : ∀ J, 0 ≤ α J - α (J + 1) := fun J => sub_nonneg.2 (hα (by omega))
  have hq1 : (1 : ℝ) ≤ q := by linarith
  constructor
  · intro J hJ
    induction J, hJ using Int.leInductionDown with
    | base => exact le_rfl
    | pred n hn ih =>
      have h1 := hf (n - 1)
      have h2 := hd (n - 1)
      rw [sub_add_cancel] at h1 h2
      have h3 : q ^ (1 : ℤ) ≤ q ^ (r - (n - 1)) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_one] at h3
      nlinarith [mul_nonneg h2 (show 0 ≤ q ^ (r - (n - 1)) - 2 by linarith)]
  · intro J hJ
    induction J, hJ using Int.leInduction with
    | base =>
      have h1 := hf r
      rw [sub_self, zpow_zero, sub_self, mul_zero] at h1
      linarith
    | succ n hn ih =>
      have h1 := hf n
      have h2 := hd n
      have h3 : q ^ (r - n) ≤ q ^ (-1 : ℤ) := zpow_le_zpow_right₀ hq1 (by omega)
      rw [zpow_neg_one] at h3
      have h4 : q⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hq
      nlinarith [mul_nonneg h2 (show 0 ≤ 2⁻¹ - q ^ (r - n) by linarith)]

theorem window_ineq : ∀ (p h : ℕ), 1 < p → 0 < h → ∀ a ρ : ℤ → ℝ, (∀ J, 0 < a J) → (∀ J, 0 < ρ J) → Antitone a → a 0 < p * a ((h : ℤ) - 1) → (∀ J, a (J + h) = a J / p) → (∀ J, ρ (J + h) = ρ J ^ ((p : ℝ) ^ h)⁻¹) → (∀ J, a (J + 1) * ρ (J + 1) ^ ((p : ℝ) ^ J) = a J * ρ J ^ ((p : ℝ) ^ J)) → ∀ r : ℕ, r < h → ∀ J : ℤ, a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) ∧ (J < 0 → a J * ρ J ^ ((p : ℝ) ^ r) < a r * ρ r ^ ((p : ℝ) ^ r)) ∧ (J ≤ -(h : ℤ) → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) ∧ (3 * (h : ℤ) ≤ J → a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p) := by
  intro p h hp hh a ρ ha hρ hanti hlt hper _ hrel r hr J
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set α : ℤ → ℝ := fun J => Real.log (a J) with hαdef
  set f : ℤ → ℝ := fun J => Real.log (a J * ρ J ^ ((p : ℝ) ^ r)) with hfdef
  have hα : Antitone α := fun i j hij => Real.log_le_log (ha j) (hanti hij)
  have hpos : ∀ J, 0 < a J * ρ J ^ ((p : ℝ) ^ r) := fun J =>
    mul_pos (ha J) (Real.rpow_pos_of_pos (hρ J) _)
  have hlog : ∀ (J : ℤ) (e : ℝ), Real.log (a J * ρ J ^ e) = α J + e * Real.log (ρ J) := by
    intro J e
    rw [Real.log_mul (ha J).ne' (Real.rpow_pos_of_pos (hρ J) _).ne', Real.log_rpow (hρ J)]
  have hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * ((p : ℝ) ^ ((r : ℤ) - J) - 1) := by
    intro J
    have h1 := congrArg Real.log (hrel J)
    rw [hlog, hlog] at h1
    have h2 : (p : ℝ) ^ r = (p : ℝ) ^ ((r : ℤ) - J) * (p : ℝ) ^ J := by
      rw [← zpow_add₀ hp0.ne', sub_add_cancel, zpow_natCast]
    simp only [hfdef, hlog]
    rw [h2]
    linear_combination (p : ℝ) ^ ((r : ℤ) - J) * h1
  obtain ⟨hL, hR⟩ := window_additive p hp2 r α f hα hf
  have hαper : ∀ J, α (J + h) = α J - Real.log p := by
    intro J
    simp only [hαdef]
    rw [hper, Real.log_div (ha J).ne' hp0.ne']
  have hdiv : f J ≤ f r - Real.log p →
      a J * ρ J ^ ((p : ℝ) ^ r) ≤ a r * ρ r ^ ((p : ℝ) ^ r) / p := by
    intro H
    rw [← Real.log_le_log_iff (hpos J) (div_pos (hpos r) hp0),
      Real.log_div (hpos r).ne' hp0.ne']
    exact H
  have hr0 : α r ≤ α 0 := hα (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.log_le_log_iff (hpos J) (hpos r)]
    change f J ≤ f r
    rcases le_or_gt J r with hJ | hJ
    · have := hL J hJ
      have := hα hJ
      linarith
    · have := hR J hJ
      have := hα (show (r : ℤ) + 1 ≤ J from hJ)
      linarith
  · intro hJ
    rw [← Real.log_lt_log_iff (hpos J) (hpos r)]
    change f J < f r
    have h1 := hL J (by omega)
    have h2 : α (-1) ≤ α J := hα (by omega)
    have h3 : α 0 < α (-1) := by
      apply Real.log_lt_log (ha 0)
      have h4 := hlt
      have h5 := hper (-1)
      rw [show (-1 : ℤ) + h = (h : ℤ) - 1 by ring] at h5
      rw [h5, mul_div_cancel₀ _ hp0.ne'] at h4
      exact h4
    linarith
  · intro hJ
    apply hdiv
    have h1 := hL J (by omega)
    have h2 : α (-h) ≤ α J := hα hJ
    have h3 := hαper (-h)
    rw [neg_add_cancel] at h3
    linarith
  · intro hJ
    apply hdiv
    have h1 := hR J (by omega)
    have h2 : α J ≤ α (h + h + h) := hα (by omega)
    have h3 := hαper (h + h)
    have h4 := hαper h
    have h5 : α h ≤ α (r + 1) := hα (by omega)
    linarith

end GlobalTheory.PMonE
