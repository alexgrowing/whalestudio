import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.UncutHalf

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

theorem kerSplit_lInt_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]
    (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) (τ : ℝ)
    (U V : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (x : H E a b) :
    lInt D k₁ k₂ τ (U - V) x = lInt D k₁ k₂ τ U x - lInt D k₁ k₂ τ V x := by
  simp only [lInt, _root_.sub_apply, inner_sub_right, Finset.sum_sub_distrib, mul_sub]

theorem kerSplit : KerSplit := by
  intro E _ _ _ n D π ι _ k₁ k₂ τ C N hb U _ _
  set S := piSp D π ι with hS
  set W := U ∘L Sᗮ.subtypeL with hW
  refine ⟨U ∘L S.starProjection, ⟨fun f hf => ?_, fun f hf => ?_⟩, ?_, ?_⟩
  · rw [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.2 hf]
  · rw [ContinuousLinearMap.comp_apply, (Submodule.starProjection_apply_eq_zero_iff S).2 hf, map_zero]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U) fun f => ?_
    calc ‖(U ∘L S.starProjection) f‖ = ‖U (S.starProjection f)‖ := rfl
      _ ≤ ‖U‖ * ‖S.starProjection f‖ := U.le_opNorm _
      _ ≤ ‖U‖ * ‖f‖ := mul_le_mul_of_nonneg_left (S.norm_starProjection_apply_le f) (norm_nonneg U)
  · set V := U - U ∘L S.starProjection with hV
    have hWU : ‖W‖ ≤ ‖U‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg U) fun f => ?_
      exact U.le_opNorm (f : Hs (ι := ι) D)
    have hVW : ‖V‖ ≤ ‖W‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg W) fun f => ?_
      have h1 : V f = W ⟨Sᗮ.starProjection f, Sᗮ.starProjection_apply_mem f⟩ := by
        change U f - U (S.starProjection f) = U (Sᗮ.starProjection f)
        rw [Submodule.starProjection_orthogonal_val, map_sub]
      rw [h1]
      refine (W.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg W))
      exact Sᗮ.norm_starProjection_apply_le f
    have hint : ∫ x, lInt D k₁ k₂ τ U x ∂D.ν - ∫ x, lInt D k₁ k₂ τ (U ∘L S.starProjection) x ∂D.ν =
        ∫ x, lInt D k₁ k₂ τ V x ∂D.ν := by
      rw [← integral_sub (hb U).1 (hb _).1]
      congr 1
      funext x
      rw [hV, kerSplit_lInt_sub]
    rw [hint]
    have hc := (hb V).2
    have hU0 : 0 ≤ C * (1 + τ) ^ N * ‖U‖ := (norm_nonneg _).trans (hb U).2
    rcases le_or_gt 0 (C * (1 + τ) ^ N) with hc0 | hc0
    · exact hc.trans (mul_le_mul_of_nonneg_left hVW hc0)
    · have hUz : ‖U‖ = 0 := le_antisymm
        (not_lt.1 fun h => absurd hU0 (not_le.2 (mul_neg_of_neg_of_pos hc0 h))) (norm_nonneg U)
      have hWz : ‖W‖ = 0 := le_antisymm (hWU.trans hUz.le) (norm_nonneg W)
      have hVz : ‖V‖ = 0 := le_antisymm (hVW.trans hWz.le) (norm_nonneg V)
      rw [hWz, mul_zero]
      rw [hVz, mul_zero] at hc
      exact hc

end DiscreteGroups.T1.G

end
