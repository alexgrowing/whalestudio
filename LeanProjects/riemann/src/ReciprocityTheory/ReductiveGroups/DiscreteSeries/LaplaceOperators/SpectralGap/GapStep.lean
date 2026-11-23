import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.GapLapStepGapStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem gapLap_stepGap : GapLapStepGapStatement := by
  intro n ε lam h hp hq hG
  obtain ⟨-, -, hN⟩ := hG
  unfold hNeed at hN
  have h1 := lt_of_le_of_lt (le_max_left _ _) hN
  have h3 := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hcast : (((qOf ε - 1 : ℕ) : ℕ) : ℝ) = (qOf ε : ℝ) - 1 := by
    rw [Nat.cast_sub hq, Nat.cast_one]
  have hm : (1 : ℝ) ≤ (min (pOf ε) (qOf ε) : ℕ) := by
    exact_mod_cast le_min hp hq
  have hs : 0 < Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨by linarith, ?_⟩
  rw [hcast, lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  linarith
