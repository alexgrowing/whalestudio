import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CuspPair

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped Pointwise

namespace DiscreteGroups.T1.G.CP

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem bound_of_hasCompactSupport {u : ℝ → ℂ} (hus : HasCompactSupport u) :
    ∃ R0 : ℝ, ∀ s, u s ≠ 0 → |s| ≤ R0 := by
  obtain ⟨R0, hR0'⟩ := (hus.isCompact.isBounded).subset_closedBall 0
  refine ⟨R0, fun s hs => ?_⟩
  have h := hR0' (subset_tsupport u hs)
  rwa [mem_closedBall_zero_iff, Real.norm_eq_abs] at h

theorem cp_supp (D : Dom E n 0) (hvol : ∀ R : ℝ, D.ν {x | |ldet x| ≤ R} < ⊤) {u : ℝ → ℂ}
    (hus : HasCompactSupport u) : D.ν {x | u (ldet x) ≠ 0} < ⊤ := by
  obtain ⟨R0, hR0⟩ := bound_of_hasCompactSupport hus
  exact lt_of_le_of_lt (measure_mono fun x hx => hR0 _ hx) (hvol R0)

end DiscreteGroups.T1.G.CP

end
