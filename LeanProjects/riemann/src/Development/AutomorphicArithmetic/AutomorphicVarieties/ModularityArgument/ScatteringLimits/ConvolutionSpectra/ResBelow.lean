import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvNear
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem side {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Sc H V W)
    (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (k : Ker β) (hB : ∀ u, B (M.J u) = M.J (conv β u)) (f : ℕ → H)
    (q0 : Tendsto (fun n => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t (f n) - f n‖ ^ 2) atTop (𝓝 0))
    (p : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0)) :
    Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) ∧
      Tendsto (fun n => M.P (Ioi M.T₀) (B (f n))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := convNear β k
  have a : Tendsto (fun n => B (f n) - M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) atTop (𝓝 0) := by
    have := (q0.const_mul C).sqrt
    rw [mul_zero, Real.sqrt_zero] at this
    refine squeeze_zero_norm (fun n => Real.le_sqrt_of_sq_le ?_) this
    obtain ⟨u, hu⟩ := M.J.surjective (f n)
    simp only [← hu, hB, M.J.symm_apply_apply, M.hJ, ← map_sub, M.J.norm_map]
    exact hC u
  refine ⟨a, ?_⟩
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L (symb β 0).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp a).add ((G.continuous.tendsto 0).comp p)
  simp only [map_zero, add_zero] at this
  refine this.congr fun n => ?_
  have e : G (M.P (Ioi M.T₀) (f n)) = M.P (Ioi M.T₀) (M.J ((symb β 0).compLpL 2 volume (M.J.symm (f n)))) := by
    show M.J ((symb β 0).compLpL 2 volume (M.J.symm (M.J (cut V _ _)))) = M.J (cut V _ (M.J.symm (M.J _)))
    rw [M.J.symm_apply_apply, M.J.symm_apply_apply]
    refine congrArg M.J (Lp.ext ?_)
    filter_upwards [(symb β 0).coeFn_compLpL (cut V (Ioi M.T₀) (M.J.symm (f n))), (symb β 0).coeFn_compLpL (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi (M.J.symm (f n)),
      cutSpec (Ioi M.T₀) measurableSet_Ioi ((symb β 0).compLpL 2 volume (M.J.symm (f n)))] with x h1 h2 h3 h4
    erw [h1, h3, h4]
    by_cases hx : x ∈ Ioi M.T₀
    · rw [indicator_of_mem hx, indicator_of_mem hx, h2]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, map_zero]
  simp only [Function.comp_apply, map_sub, e, sub_add_cancel]

theorem UpperTheory.V.Z.IntegralApplyAeEq.resBelow :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      ∀ f : ℕ → H, (∀ n, ‖f n‖ = 1) → Tendsto (fun n => M.abelian₂ M.T₀ M.T₀ (f n) - f n) atTop (𝓝 0) →
        Tendsto (fun n => (⟪f n, M.F.av wR (f n)⟫_ℂ).re) atTop (𝓝 1) → False := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc f hf t1 t2
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  obtain ⟨-, -, -, -, -, -, l2, -, l4⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  let q : H → ℝ := fun h => ∫ t in Iic (0 : ℝ), Real.exp t * ‖M.F.U t h - h‖ ^ 2
  have q0 : Tendsto (fun n => q (f n)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub (t2.const_mul 2)
    simp only [mul_one, sub_self] at this
    exact this.congr fun n => by simp only [q, (resCob M.F _).2, hf]; ring
  have p1 : Tendsto (fun n => M.P (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l2 _
      simp [l]
  have p2 : Tendsto (fun n => M.P' (Ioi M.T₀) (f n)) atTop (𝓝 0) := by
    have := (((M.P' (Ioi M.T₀)).continuous.tendsto 0).comp t1).neg
    simp only [map_zero, neg_zero] at this
    exact this.congr fun n => by
      have l : M.P' (Ioi M.T₀) (Λ (f n)) = 0 := DFunLike.congr_fun l4 _
      simp [l]
  obtain ⟨a1, a2⟩ := side M B β k1 ha.1 f q0 p1
  obtain ⟨-, a3⟩ := side M.swap B β' k2 ha.2 f (q0.congr fun n => by
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    show _ = Real.exp t * ‖M.F.U (-t) (f n) - f n‖ ^ 2
    rw [← M.F.norm t (M.F.U (-t) (f n) - f n), map_sub, ← M.F.add, add_neg_cancel, M.F.zero, norm_sub_rev]) p2
  have a4 : Tendsto (fun n => B (f n) - (Λ ∘L B ∘L Λ) (f n)) atTop (𝓝 0) := by
    have := (a2.add a3).sub (((Λ ∘L B).continuous.tendsto 0).comp t1)
    simp only [map_zero, add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    have e : Λ (B (f n)) = B (f n) - M.P (Ioi M.T₀) (B (f n)) - M.swap.P (Ioi M.swap.T₀) (B (f n)) := rfl
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_sub, e]
    abel
  obtain ⟨S, hS, hsub⟩ := hc.image_closedBall_subset_compact 1
  obtain ⟨y, -, φ, hφ, hy⟩ := hS.tendsto_subseq fun n => hsub ⟨f n, by simp [hf], rfl⟩
  obtain ⟨s, hs⟩ := u1
  let G : H →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L ((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume ∘L
    (M.J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
  have hG : ∀ h, G (M.J ((symb β 0).compLpL 2 volume (M.J.symm h))) = h := fun h => by
    show M.J (((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).compLpL 2 volume (M.J.symm (M.J _))) = h
    rw [M.J.symm_apply_apply, ← M.J.eq_symm_apply]
    refine Lp.ext ?_
    filter_upwards [((s⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V).coeFn_compLpL ((symb β 0).compLpL 2 volume (M.J.symm h)),
      (symb β 0).coeFn_compLpL (M.J.symm h)] with x h1 h2
    rw [h1, h2, ← hs]
    exact DFunLike.congr_fun s.inv_mul _
  have c1 : Tendsto (fun n => f (φ n)) atTop (𝓝 (G y)) := by
    have := (G.continuous.tendsto _).comp ((hy.add (a4.comp hφ.tendsto_atTop)).sub (a1.comp hφ.tendsto_atTop))
    simp only [add_zero, sub_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.coe_coe, add_sub_cancel, sub_sub_cancel, hG]
  set g := G y
  have g1 : ‖g‖ = 1 := tendsto_nhds_unique c1.norm (by simp [hf])
  have qc : Continuous q := by
    simp only [q, (resCob M.F _).2]
    fun_prop
  have g2 : q g = 0 := tendsto_nhds_unique ((qc.tendsto g).comp c1) (q0.comp hφ.tendsto_atTop)
  have cg : Continuous fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2 := by
    have := M.F.cont g
    fun_prop
  have ig : IntegrableOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) (Iic 0) := by
    refine Integrable.mono' ((integrableOn_exp_Iic 0).mul_const 4) cg.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : ‖M.F.U t g - g‖ ≤ 2 := (norm_sub_le _ _).trans_eq (by rw [M.F.norm, g1]; norm_num)
    gcongr
    nlinarith [norm_nonneg (M.F.U t g - g)]
  have g3 := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun t => by positivity) ig).1 g2
  have g4 : EqOn (fun t => Real.exp t * ‖M.F.U t g - g‖ ^ 2) 0 (Iio 0) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset Iio_subset_Iic_self g3) isOpen_Iio cg.continuousOn
      continuousOn_const
  have g5 : ∀ᶠ t in atBot, ⟪g, M.F.U t g⟫_ℂ = 1 := by
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    have := g4 ht
    simp only [Pi.zero_apply, mul_eq_zero, (Real.exp_pos t).ne', false_or, pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at this
    rw [this, inner_self_eq_norm_sq_to_K, g1]; simp
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' (g5.mono fun _ h => h.symm)) ((projLaws M).1 g g).2)
