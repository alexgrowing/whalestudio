import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.Analysis

theorem tendsto_factorial_mul_div_pow_of_eps_bounds (f : ℕ → ℝ) (G : ℝ) (D : ℕ)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) :
    Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  have hfac : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast D.factorial_pos
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hl ((G - a) / 2) (by linarith), hev] with n hn hp
    rw [div_le_iff₀ hfac] at hn
    have key : G - (G - a) / 2 ≤ (D.factorial : ℝ) * f n / (n : ℝ) ^ D := by
      rw [le_div_iff₀ hp]
      linarith
    linarith
  · filter_upwards [hu ((b - G) / 2) (by linarith), hev] with n hn hp
    rw [le_div_iff₀ hfac] at hn
    have key : (D.factorial : ℝ) * f n / (n : ℝ) ^ D ≤ G + (b - G) / 2 := by
      rw [div_le_iff₀ hp]
      linarith
    linarith

end GlobalTheory.CompanionTheory.Analysis
