import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cobLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H), F.Cob 0 ∧ (∀ h h', F.Cob h → F.Cob h' → F.Cob (h + h') ∧ F.Cob (h - h')) ∧ (∀ (c : ℂ) h, F.Cob h → F.Cob (c • h)) ∧
      (∀ h, F.rev.Cob h ↔ F.Cob h) ∧ (∀ s h, F.Cob (h - F.U s h)) ∧ (∀ h, F.Cob h → ∃ C, ∀ t, ‖∫ s in (0 : ℝ)..t, F.U s h‖ ≤ C) ∧
      (F.Null → ∀ h h' (c : ℝ), F.Cob h → Tendsto (fun a => ∫ s in (c - a)..(c + a), ⟪h', F.U s h⟫_ℂ) atTop (𝓝 0)) ∧
      ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F' : Flow G) (Y : H →L[ℂ] G), (∀ t h, Y (F.U t h) = F'.U t (Y h)) → ∀ h, F.Cob h → F'.Cob (Y h) := by
  intro H _ _ _ F
  have ii : ∀ h a b, IntervalIntegrable (fun s => F.U s h) volume a b := fun h a b => (F.cont h).intervalIntegrable a b
  have hs : ∀ (c : ℂ) h, F.Cob h → F.Cob (c • h) := fun c h ⟨k, hk⟩ =>
    ⟨c • k, fun t => by simp only [map_smul]; rw [intervalIntegral.integral_smul, hk, smul_sub]⟩
  have ha : ∀ h h', F.Cob h → F.Cob h' → F.Cob (h + h') := fun h h' ⟨k, hk⟩ ⟨k', hk'⟩ =>
    ⟨k + k', fun t => by simp only [map_add]; rw [intervalIntegral.integral_add (ii _ _ _) (ii _ _ _), hk, hk']; abel⟩
  have hr : ∀ (F : Flow H) h, F.Cob h → F.rev.Cob h := fun F h ⟨k, hk⟩ => ⟨-k, fun t => by
    show ∫ s in (0 : ℝ)..t, F.U (-s) h = F.U (-t) (-k) - -k
    rw [intervalIntegral.integral_comp_neg fun s => F.U s h, neg_zero, intervalIntegral.integral_symm, hk, map_neg]; abel⟩
  refine ⟨⟨0, fun t => by simp⟩, fun h h' a b => ⟨ha _ _ a b, ?_⟩, hs, fun h => ⟨fun x => ?_, hr F h⟩, fun s h => ?_,
    fun h ⟨k, hk⟩ => ⟨‖k‖ + ‖k‖, fun t => ?_⟩, fun hn h h' c ⟨k, hk⟩ => ?_, ?_⟩
  · simpa [sub_eq_add_neg] using ha _ _ a (hs (-1) _ b)
  · obtain ⟨k, hk⟩ := hr F.rev h x
    exact ⟨k, fun t => by simpa [Flow.rev] using hk t⟩
  · refine ⟨-∫ r in (0 : ℝ)..s, F.U r h, fun t => ?_⟩
    simp only [map_sub, ← F.add]
    have hc : Continuous fun r => F.U (r + s) h := (F.cont h).comp (continuous_id.add continuous_const)
    rw [intervalIntegral.integral_sub (ii _ _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_comp_add_right fun r => F.U r h, map_neg, ← (F.U t).intervalIntegral_comp_comm (ii _ _ _)]
    simp only [← F.add]
    rw [intervalIntegral.integral_comp_add_left fun r => F.U r h, zero_add, add_zero]
    have e1 := intervalIntegral.integral_add_adjacent_intervals (ii h 0 t) (ii h t (t + s))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (ii h 0 s) (ii h s (t + s))
    rw [eq_sub_of_add_eq e1, ← e2]; abel
  · rw [hk]; exact (norm_sub_le _ _).trans_eq (by rw [F.norm])
  · have e : ∀ a, ∫ s in (c - a)..(c + a), ⟪h', F.U s h⟫_ℂ = ⟪h', F.U (c + a) k⟫_ℂ - ⟪h', F.U (c - a) k⟫_ℂ := fun a => by
      have := (innerSL ℂ h').intervalIntegral_comp_comm (ii h (c - a) (c + a))
      simp only [innerSL_apply_apply] at this
      rw [this, ← intervalIntegral.integral_interval_sub_left (ii h 0 _) (ii h 0 _), hk, hk, ← inner_sub_right]
      congr 1; abel
    simp only [e]
    simpa [sub_eq_add_neg] using ((hn k h').1.comp (tendsto_atTop_add_const_left _ c tendsto_id)).add
      ((hn k h').2.comp (tendsto_atBot_add_const_left _ c tendsto_neg_atTop_atBot)).neg
  · intro G _ _ _ F' Y hY h ⟨k, hk⟩
    exact ⟨Y k, fun t => by simp only [← hY]; rw [Y.intervalIntegral_comp_comm (ii _ _ _), hk, map_sub]⟩
