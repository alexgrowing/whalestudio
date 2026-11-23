import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLim

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.shNull :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V], (shF V).Null := by
  intro V _ _ _ _
  have top : ∀ u u' : L V, Tendsto (fun t => ⟪u', sh V t u⟫_ℂ) atTop (𝓝 0) := by
    intro u u'
    have hi : Integrable fun x => ‖u' x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u')).1 (Lp.memLp u')
    have h1 := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x => ‖u' x‖ ^ 2) (s := fun T : ℝ => Iic (-T))
      (fun _ => measurableSet_Iic) (fun x y h => Iic_subset_Iic.2 (by linarith)) ⟨0, hi.integrableOn⟩
    have he : ⋂ T : ℝ, Iic (-T) = ∅ := eq_empty_of_forall_notMem fun x hx => by
      have := mem_iInter.1 hx (1 - x)
      simp at this; linarith
    rw [he, setIntegral_empty] at h1
    have h2 : Tendsto (fun T : ℝ => ‖cut V (Iic (-T)) u'‖ * ‖u‖) atTop (𝓝 0) := by
      have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).mul_const ‖u‖
      rw [Real.sqrt_zero, zero_mul] at h2
      refine h2.congr fun T => ?_
      rw [Function.comp_apply, ← (cutLaws (V := V) _ univ measurableSet_Iic .univ).2.2.2.2.2.2.2.2 u', Real.sqrt_sq (norm_nonneg _)]
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨T, hT⟩ := (h2.eventually (gt_mem_nhds (half_pos hε))).exists
    have h3 : Tendsto (fun t => ‖⟪u', cut V (Ioi (-T)) (sh V t u)⟫_ℂ‖) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := u')).inner (𝕜 := ℂ) ((cutLim u).1 (-T))).norm
    filter_upwards [h3.eventually (gt_mem_nhds (half_pos hε))] with t ht
    obtain ⟨-, c2, c3, c4, -⟩ := cutLaws (V := V) (Iic (-T)) (Ioi (-T)) measurableSet_Iic measurableSet_Ioi
    have h4 := c3 (Iic_disjoint_Ioi le_rfl)
    rw [Iic_union_Ioi, c4] at h4
    have h5 : sh V t u = cut V (Iic (-T)) (sh V t u) + cut V (Ioi (-T)) (sh V t u) := DFunLike.congr_fun h4 _
    rw [h5, inner_add_right, ← c2.isSymmetric.apply_clm]
    refine (norm_add_le _ _).trans_lt ?_
    have h6 := norm_inner_le_norm (𝕜 := ℂ) (cut V (Iic (-T)) u') (sh V t u)
    rw [show ‖sh V t u‖ = ‖u‖ from (shF V).norm t u] at h6
    linarith
  refine fun u u' => ⟨top u u', ?_⟩
  have h1 := (Complex.continuous_conj.tendsto 0).comp ((top u' u).comp tendsto_neg_atBot_atTop)
  rw [map_zero] at h1
  refine h1.congr fun t => ?_
  have hin := (⟨(sh V t : L V →ₗ[ℂ] L V), (shF V).norm t⟩ : L V →ₗᵢ[ℂ] L V).inner_map_map (sh V (-t) u') u
  have e : sh V t (sh V (-t) u') = u' := by
    have := (shF V).add t (-t) u'
    rw [add_neg_cancel, (shF V).zero] at this
    exact this.symm
  simp only [Function.comp_apply, inner_conj_symm]
  rw [← hin]
  show ⟪sh V t (sh V (-t) u'), sh V t u⟫_ℂ = _
  rw [e]; rfl
