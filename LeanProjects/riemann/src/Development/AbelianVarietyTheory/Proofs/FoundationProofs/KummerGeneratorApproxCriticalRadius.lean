import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsImprovedApproxKummerGeneratorStatement
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem kummer_approx_critical : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → v (p : L) < 1 → ∀ α : L, α ^ p ∈ F → 0 < v (p : L) →
    ∀ s : ℝ≥0, 1 < s → ∃ y ∈ F, v (α - y) ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := by
  intro L _ v p hp F hF hvp α hα hvp0 s hs
  obtain ⟨θ, hθ, hθF⟩ := hF
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : p - 1 ≠ 0 := by omega
  by_cases hα0 : α = 0
  · refine ⟨0, F.zero_mem, ?_⟩
    simp [hα0, zero_pow hp1]
  by_contra hcon
  push_neg at hcon
  have hs0 : (0 : ℝ≥0) < s := zero_lt_one.trans hs
  have ha : 0 < v α := (Valuation.pos_iff v).2 hα0
  set a := v α with ha_def
  set c := s * v (p : L) * a ^ (p - 1) with hc_def
  have hc : 0 < c := by positivity
  set η : ℝ≥0 := max s⁻¹ (max θ (v (p : L))) with hη_def
  have hη : η < 1 := by
    simp only [hη_def, max_lt_iff]
    exact ⟨inv_lt_one_of_one_lt₀ hs, hθ, hvp⟩
  have step : ∀ y ∈ F, v (α - y) ≤ a → ∃ y' ∈ F, v (α - y') ^ p ≤ η * v (α - y) ^ p := by
    intro y hy hya
    obtain ⟨y', hy', h⟩ := GlobalTheory.T.exists_improved_approx_kummer_generator L v p hp F θ hθ.le hvp.le hθF α y hα hy hya
    refine ⟨y', hy', h.trans ?_⟩
    have hcb := hcon y hy
    set b := v (α - y)
    apply max_le
    · have h0 : s * (v (p : L) * a ^ (p - 1)) ≤ b ^ (p - 1) := by
        calc s * (v (p : L) * a ^ (p - 1)) = c := by rw [hc_def]; ring
          _ ≤ _ := hcb.le
      have h2 : v (p : L) * a ^ (p - 1) ≤ s⁻¹ * b ^ (p - 1) := by
        calc v (p : L) * a ^ (p - 1) = s⁻¹ * (s * (v (p : L) * a ^ (p - 1))) := (inv_mul_cancel_left₀ hs0.ne' _).symm
          _ ≤ s⁻¹ * b ^ (p - 1) := by gcongr
      have h1 : v (p : L) * b * a ^ (p - 1) ≤ s⁻¹ * b ^ p := by
        calc v (p : L) * b * a ^ (p - 1) = b * (v (p : L) * a ^ (p - 1)) := by ring
          _ ≤ b * (s⁻¹ * b ^ (p - 1)) := by gcongr
          _ = s⁻¹ * (b ^ (p - 1) * b) := by ring
          _ = s⁻¹ * b ^ p := by rw [← pow_succ]; congr 2; omega
      exact h1.trans (by gcongr; exact le_max_left _ _)
    · gcongr; exact le_max_right _ _
  have iter : ∀ k : ℕ, ∃ y ∈ F, v (α - y) ≤ a ∧ v (α - y) ^ p ≤ η ^ k * a ^ p := by
    intro k
    induction k with
    | zero => exact ⟨0, F.zero_mem, by simp [ha_def], by simp [ha_def]⟩
    | succ k ih =>
      obtain ⟨y, hy, hya, hyk⟩ := ih
      obtain ⟨y', hy', h'⟩ := step y hy hya
      have hle : v (α - y') ^ p ≤ v (α - y) ^ p :=
        h'.trans (mul_le_of_le_one_left (by positivity) hη.le)
      refine ⟨y', hy', ?_, ?_⟩
      · exact ((pow_le_pow_iff_left₀ (by positivity) (by positivity) hp.ne_zero).1 hle).trans hya
      · calc v (α - y') ^ p ≤ η * v (α - y) ^ p := h'
          _ ≤ η * (η ^ k * a ^ p) := by gcongr
          _ = η ^ (k + 1) * a ^ p := by ring
  have hA : 0 < (a ^ p) ^ (p - 1) := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (pow_pos hc p) hA) hη
  obtain ⟨y, hy, -, hyk⟩ := iter k
  have hcb := hcon y hy
  have e1 : c ^ p < (v (α - y) ^ p) ^ (p - 1) := by
    calc c ^ p < (v (α - y) ^ (p - 1)) ^ p := pow_lt_pow_left₀ hcb (by positivity) hp.ne_zero
      _ = _ := by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : (v (α - y) ^ p) ^ (p - 1) ≤ η ^ k * (a ^ p) ^ (p - 1) := by
    calc (v (α - y) ^ p) ^ (p - 1) ≤ (η ^ k * a ^ p) ^ (p - 1) := pow_le_pow_left₀ (by positivity) hyk _
      _ = (η ^ k) ^ (p - 1) * (a ^ p) ^ (p - 1) := mul_pow _ _ _
      _ ≤ η ^ k * (a ^ p) ^ (p - 1) :=
          mul_le_mul_of_nonneg_right (pow_le_of_le_one (by positivity) (pow_le_one₀ (by positivity) hη.le) hp1) (by positivity)
  have e3 : η ^ k * (a ^ p) ^ (p - 1) < c ^ p := (lt_div_iff₀ hA).1 hk
  exact lt_irrefl _ ((e1.trans_le e2).trans e3)

end GlobalTheory.AlmostEt
