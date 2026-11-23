import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem symb_diff {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) : Differentiable ℂ (symb κ) := fun z => by
  have c1 : ∀ w : ℂ, Continuous fun t : ℝ => Complex.exp (w * t) • κ t := fun w =>
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have c2 : Continuous fun t : ℝ => (Complex.exp (z * t) * t) • κ t :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul Complex.continuous_ofReal).smul hk.1
  have c3 : Continuous fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := by
    have := hk.1
    fun_prop
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  have s3 : HasCompactSupport fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := hk.2.mono fun t ht h => ht (by simp [h])
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun (w : ℂ) (t : ℝ) => Complex.exp (w * t) • κ t)
    (F' := fun (w : ℂ) (t : ℝ) => (Complex.exp (w * t) * t) • κ t) (bound := fun t => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖)
    (Metric.ball_mem_nhds z one_pos) (Eventually.of_forall fun w => (c1 w).aestronglyMeasurable)
    ((c1 z).integrable_of_hasCompactSupport s1) c2.aestronglyMeasurable
    (Eventually.of_forall fun t w hw => ?_) (c3.integrable_of_hasCompactSupport s3)
    (Eventually.of_forall fun t w _ => ?_)).2.differentiableAt
  · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    have := norm_sub_norm_le w z
    rw [Metric.mem_ball, dist_eq_norm] at hw
    linarith
  · simpa using (((hasDerivAt_id w).mul_const (t : ℂ)).cexp).smul_const (κ t)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convDense :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → IsUnit (symb β 0) → DenseRange (conv β) := by
  intro V _ _ _ _ β hk hu
  obtain ⟨k1, k2, k3⟩ := convAdj β hk
  let D : ℂ → ℂ := fun z => LinearMap.det (symb (sharp β) z : V →ₗ[ℂ] V)
  have hD : Differentiable ℂ D := by
    let b := Module.finBasis ℂ V
    have e : D = fun z => ∑ s : Equiv.Perm (Fin (Module.finrank ℂ V)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
        ∏ i, (b.coord (s i)).toContinuousLinearMap (symb (sharp β) z (b i)) := by
      funext z
      simp only [D]
      rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
      simp [LinearMap.toMatrix_apply]
    rw [e]
    refine Differentiable.fun_sum fun s _ => (differentiable_const _).mul (Differentiable.fun_finset_prod fun i _ => ?_)
    exact (ContinuousLinearMap.differentiable _).comp ((symb_diff _ k1).clm_apply (differentiable_const _))
  have h0 : D 0 ≠ 0 := by
    have : IsUnit (symb (sharp β) 0) := by
      rw [k3, map_zero, neg_zero]; exact hu.star
    exact ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 (ContinuousLinearMap.isUnit_iff_bijective.1 this))).ne_zero
  let g : ℝ → ℂ := fun ξ => D (2 * Real.pi * Complex.I * ξ)
  have ga : AnalyticOnNhd ℝ g univ := fun ξ _ => by
    have h1 : AnalyticAt ℝ (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)) ξ :=
      analyticAt_const.mul (Complex.ofRealCLM.analyticAt ξ)
    exact (hD.analyticAt _).restrictScalars.comp h1
  have gz : ∀ᵐ ξ : ℝ, g ξ ≠ 0 := by
    have h1 := ga.preimage_zero_mem_codiscreteWithin (x := 0) (by simpa [g] using h0) trivial isConnected_univ
    have h2 := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ h1
    rw [Measure.restrict_univ] at h2
    exact h2
  have inj : ∀ y : L V, conv (sharp β) y = 0 → y = 0 := fun y hy => by
    rw [← (Lp.fourierTransformₗᵢ ℝ V).map_eq_zero_iff]
    refine Lp.ext ?_
    have h1 := fourConv (sharp β) k1 y
    rw [hy, map_zero] at h1
    filter_upwards [h1, gz, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with ξ a b c
    rw [c] at a ⊢
    have := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit b))).1
    exact this (a₁ := _) (a₂ := 0) (a.symm.trans (map_zero _).symm)
  have bot : (LinearMap.range (conv β : L V →ₗ[ℂ] L V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine inj y (ext_inner_left ℂ fun x => ?_)
    rw [← k2, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact hy _ ⟨x, rfl⟩
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 (Submodule.topologicalClosure_eq_top_iff.2 bot)
