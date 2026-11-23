import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem walkEnds : EndsStatement := by
  intro k r u v b t
  refine ⟨?_, ?_, ?_⟩
  · funext a
    have ha := a.isLt
    simp only [lamT, raisePar]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
      | (have h0 : a.val - (k - 1) = 0 := by omega
         simp [h0])
  · funext a
    have ha := a.isLt
    simp only [raisePar, walkPar, parLam]
    split_ifs
    all_goals first
      | rfl
      | (exfalso; omega)
  · funext a
    simp [walkPar]

end ReciprocityTheory.ChartRestriction.DS.Lap
