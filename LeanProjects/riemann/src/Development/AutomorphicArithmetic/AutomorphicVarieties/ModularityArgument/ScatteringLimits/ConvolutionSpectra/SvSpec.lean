import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.svSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V], (∀ φ : ℝ → ℂ, MemLp φ 2 volume → ∀ e : V, (∀ᵐ x : ℝ, sv V φ e x = φ x • e) ∧ ‖sv V φ e‖ ^ 2 = (∫ x, ‖φ x‖ ^ 2) * ‖e‖ ^ 2) ∧
      ∀ e : V, (∀ᵐ x : ℝ, one V e x = (Ioc (0 : ℝ) 1).indicator (fun _ => e) x) ∧ Bdd (one V e) ∧ ∫ x, one V e x = e := by
  intro V _ _ _ _
  have h0 : ∀ φ : ℝ → ℂ, MemLp φ 2 volume → ∀ e : V, ∀ᵐ x : ℝ, sv V φ e x = φ x • e := by
    intro φ hφ
    have hc : ∀ e : V, ∀ᵐ x : ℝ, (ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ) x = φ x • e := fun e => by
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLpL (hφ.toLp φ), hφ.coeFn_toLp] with x h1 h2
      rw [h1, h2]; simp
    let A : V →ₗ[ℂ] L V :=
      { toFun := fun e => (ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ)
        map_add' := fun e f => Lp.ext (by
          filter_upwards [hc (e + f), hc e, hc f, Lp.coeFn_add ((ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ))
            ((ContinuousLinearMap.toSpanSingleton ℂ f).compLpL 2 volume (hφ.toLp φ))] with x h1 h2 h3 h4
          rw [h1, h4, Pi.add_apply, h2, h3, smul_add])
        map_smul' := fun c e => Lp.ext (by
          filter_upwards [hc (c • e), hc e, Lp.coeFn_smul c ((ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ))]
            with x h1 h2 h4
          rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, smul_comm]) }
    exact Classical.epsilon_spec (p := fun C : V →L[ℂ] L V => ∀ e, ∀ᵐ x : ℝ, C e x = φ x • e)
      ⟨LinearMap.toContinuousLinearMap A, hc⟩
  refine ⟨fun φ hφ e => ⟨h0 φ hφ e, ?_⟩, fun e => ?_⟩
  · obtain ⟨-, -, -, c4, -, -, -, -, c9⟩ := cutLaws (V := V) univ univ .univ .univ
    have := c9 (sv V φ e)
    rw [c4, Measure.restrict_univ] at this
    rw [← integral_mul_const]
    refine this.trans (integral_congr_ae ?_)
    filter_upwards [h0 φ hφ e] with x h
    rw [h, norm_smul, mul_pow]
  · have h1 : ∀ᵐ x : ℝ, one V e x = (Ioc (0 : ℝ) 1).indicator (fun _ => e) x := by
      filter_upwards [h0 _ (memLp_indicator_const 2 measurableSet_Ioc (1 : ℂ) (Or.inr (by simp : volume (Ioc (0 : ℝ) 1) ≠ ⊤))) e] with x h
      refine h.trans ?_
      by_cases b : x ∈ Ioc (0 : ℝ) 1 <;> simp [b]
    refine ⟨h1, ⟨1, ((cutLaws (V := V) _ univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩
    · filter_upwards [h1] with x h hx
      rw [h, indicator_of_notMem fun b => hx ⟨by linarith [b.1], b.2⟩]
    · rw [integral_congr_ae h1, integral_indicator measurableSet_Ioc]; simp
