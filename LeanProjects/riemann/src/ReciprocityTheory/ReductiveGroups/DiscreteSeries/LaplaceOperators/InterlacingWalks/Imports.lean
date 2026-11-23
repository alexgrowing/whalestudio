import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem seg : SegStatement := by
  intro n Q x s d N hx hstep
  have key : ∀ m : ℕ, m ≤ N → Q (x + ((m : ℝ) * d) • Pi.single s 1) := by
    intro m
    induction m with
    | zero => intro _; simpa using hx
    | succ m ih =>
      intro hm
      have h := hstep m (by omega) (ih (by omega))
      rw [Nat.cast_succ]
      exact h
  exact key N le_rfl

end ReciprocityTheory.ChartRestriction.DS.Lap
