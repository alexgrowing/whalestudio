import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Grow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nIso :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), (∀ e, M.F.Cob (M.J (one V e)) → e = 0) ∧ ∀ N, M.IsN N → ∀ w, ‖N w‖ = ‖w‖ := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M
  obtain ⟨g, hg, g1, g2⟩ := grow (V := V) (W := W)
  have hb := (cobLaws M.F).2.2.2.2.2.1
  have e1 : ∀ (e : V) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J (one V e))‖ = g t * ‖e‖ := fun e t => by
    simp only [M.hJ]
    rw [← g1, ← M.J.norm_map]
    exact congrArg _ ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).intervalIntegral_comp_comm
      (((shF V).cont _).intervalIntegrable _ _))
  have e2 : ∀ (f : W) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J' (one W f))‖ = g t * ‖f‖ := fun f t => by
    simp only [M.hJ']
    rw [← g2, ← M.J'.norm_map]
    exact congrArg _ ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).intervalIntegral_comp_comm
      (((shF W).rev.cont _).intervalIntegrable _ _))
  have key : ∀ d C : ℝ, (∀ t, |g t * d| ≤ C) → d = 0 := fun d C h => by
    by_contra hd
    have h1 : Tendsto (fun t => |g t| * |d|) atTop atTop := (tendsto_abs_atTop_atTop.comp hg).atTop_mul_const (abs_pos.2 hd)
    obtain ⟨t, ht⟩ := (h1.eventually_gt_atTop C).exists
    exact absurd (abs_mul (g t) d ▸ h t) (not_le.2 ht)
  refine ⟨fun e he => ?_, fun N hN w => ?_⟩
  · obtain ⟨C, hC⟩ := hb _ he
    exact norm_eq_zero.1 (key _ C fun t => by rw [← e1, abs_norm]; exact hC t)
  · obtain ⟨C, hC⟩ := hb _ (hN w)
    refine (sub_eq_zero.1 (key (‖w‖ - ‖N w‖) C fun t => ?_)).symm
    rw [mul_sub, ← e1, ← e2]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← intervalIntegral.integral_sub ((M.F.cont _).intervalIntegrable _ _) ((M.F.cont _).intervalIntegrable _ _)]
    simpa only [map_sub] using hC t
