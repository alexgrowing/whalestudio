import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

theorem positive_negative_holds : PosNeg := by
  intro H _ _ _ a ha
  refine ⟨cfc (fun x : ℝ => max x 0) a, cfc (fun x : ℝ => max (-x) 0) a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cfc_sub (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) a]
    conv_lhs => rw [← cfc_id' ℝ a]
    refine cfc_congr fun x _ => ?_
    exact (max_zero_sub_eq_self x).symm
  · rw [← cfc_mul (fun x : ℝ => max (-x) 0) (fun x : ℝ => max x 0) a]
    rw [← cfc_zero ℝ a]
    refine cfc_congr fun x _ => ?_
    rcases le_total x 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_right (neg_nonpos.mpr h)]
  · intro x
    have hp : 0 ≤ cfc (fun x : ℝ => max x 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).re_inner_nonneg_left x
  · intro x
    have hm : 0 ≤ cfc (fun x : ℝ => max (-x) 0) a := cfc_nonneg fun y _ => le_max_right _ _
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hm).re_inner_nonneg_left x
  · intro S hS
    exact ⟨hS.cfc_real _, hS.cfc_real _⟩

end PositivityTheory.RgHe3
