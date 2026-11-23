import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapelliQdetStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem gapCentral (n : ℕ) : GapCentralStatement n := by
  intro ε lam h ⟨_, hg, hN⟩
  unfold hNeed at hN
  have hA := (le_max_left _ _).trans_lt hN
  have hB := (le_max_right _ _).trans_lt hN
  have hB1 := (le_max_left _ _).trans_lt hB
  have hB2 := (le_max_right _ _).trans_lt hB
  have hA1 : 1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤
      max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) := le_max_right _ _
  have hM : 2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) ≤
      max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) := le_max_left _ _
  have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
  have hn : (0 : ℝ) ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
  have hP := mul_nonneg hs (by linarith : (0 : ℝ) ≤
      4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1 -
        (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ))
  exact ⟨hg, by linarith, by linarith, by nlinarith⟩

theorem hcV_of_centralChar (n : ℕ) (hCC : CentralCharStatement n) : HcVStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y hy
  have hle : V ≤ genSub E V := le_sInf fun T hT => hT.1
  exact hCC ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y (hle hy)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
