import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open scoped NNReal

namespace UpperTheory.Esk.CharacterExpansionLemmas

theorem key (ν : Valuation ℂ ℝ≥0) (τ δ : ℂ) (hτ : ν τ ≤ 1) (hδ : ν δ ≤ 1) :
    ∀ n, ν (ch τ δ n) ≤ 1 ∧ ν (ch τ δ (n + 1)) ≤ 1 ∧ ν (ch τ δ (n + 1) - τ ^ n) ≤ ν δ
  | 0 => by simp [ch]
  | n + 1 => by
    obtain ⟨h0, h1, h2⟩ := key ν τ δ hτ hδ n
    have e : ch τ δ (n + 2) = τ * ch τ δ (n + 1) - δ * ch τ δ n := rfl
    have e2 : ch τ δ (n + 2) - τ ^ (n + 1) = τ * (ch τ δ (n + 1) - τ ^ n) - δ * ch τ δ n := by
      rw [e]; ring
    refine ⟨h1, ?_, ?_⟩
    · rw [e]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
      · calc ν τ * ν (ch τ δ (n + 1)) ≤ 1 * 1 := mul_le_mul' hτ h1
          _ = 1 := one_mul _
      · calc ν δ * ν (ch τ δ n) ≤ 1 * 1 := mul_le_mul' hδ h0
          _ = 1 := one_mul _
    · rw [e2]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
      · calc ν τ * ν (ch τ δ (n + 1) - τ ^ n) ≤ 1 * ν δ := mul_le_mul' hτ h2
          _ = ν δ := one_mul _
      · calc ν δ * ν (ch τ δ n) ≤ ν δ * 1 := mul_le_mul' le_rfl h0
          _ = ν δ := mul_one _

end UpperTheory.Esk.CharacterExpansionLemmas

theorem UpperTheory.Esk.pf_GCh : UpperTheory.Esk.GCh := fun ν τ δ hτ hδ n =>
  ⟨(UpperTheory.Esk.CharacterExpansionLemmas.key ν τ δ hτ hδ n).2.1, (UpperTheory.Esk.CharacterExpansionLemmas.key ν τ δ hτ hδ n).2.2⟩
