import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

theorem KodairaGeneric.proof (hR : NefSectionGrowth.Statement) (hE : HyperplaneSectionBound.Statement) :
    KodairaGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D a hD hV hB hN hg
  obtain ⟨C₁, h₁⟩ := hR K ι Ω y D a hD hV hB hN
  obtain ⟨C₂, h₂⟩ := hE K ι Ω y D a hD hV hB
  set G : ℝ := (genDeg (mCoordIdeal y) D a : ℝ) / (D.factorial : ℝ) with hGdef
  have hG : 0 < G := div_pos (by exact_mod_cast hg) (by exact_mod_cast D.factorial_pos)
  obtain ⟨n, hn₁, hn₂, hn₃, hn₄⟩ := (h₁.and (h₂.and ((tendsto_natCast_atTop_atTop.eventually_gt_atTop ((|C₁| + |C₂|) / G)).and
    (eventually_ge_atTop (1 : ℕ))))).exists
  set f : ℝ := (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ)
  set g : ℝ := (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a - 1) 1) : ℝ)
  have hlow : (genDeg (mCoordIdeal y) D a : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) - C₁ * (n : ℝ) ^ (D - 1) ≤ f := by
    have := (abs_le.mp hn₁).1; linarith
  have hpow : (n : ℝ) ^ D = (n : ℝ) * (n : ℝ) ^ (D - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hq : 0 < (n : ℝ) ^ (D - 1) := pow_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hnG : |C₁| + |C₂| < G * n := by rw [div_lt_iff₀ hG] at hn₃; linarith
  have hmain : (|C₁| + |C₂|) * (n : ℝ) ^ (D - 1) < G * n * (n : ℝ) ^ (D - 1) :=
    mul_lt_mul_of_pos_right hnG hq
  have hGn : (genDeg (mCoordIdeal y) D a : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) =
      G * n * (n : ℝ) ^ (D - 1) := by
    rw [hGdef, hpow]; ring
  have hC : (C₁ + C₂) * (n : ℝ) ^ (D - 1) ≤ (|C₁| + |C₂|) * (n : ℝ) ^ (D - 1) :=
    mul_le_mul_of_nonneg_right (add_le_add (le_abs_self _) (le_abs_self _)) hq.le
  have hgpos : 0 < g := by nlinarith
  have hne : chartLatQ y ((n : ℤ) • a - 1) 1 ≠ ⊥ := by
    intro hbot
    have h0' : Module.finrank ℚ (chartLatQ y ((n : ℤ) • a - 1) 1) = 0 := by
      rw [hbot]; exact finrank_bot ℚ Ω
    have h0 : g = 0 := by simp only [g, h0', Nat.cast_zero]
    linarith
  obtain ⟨e, he, he0⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨n, e, hn₄, he0, he⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
