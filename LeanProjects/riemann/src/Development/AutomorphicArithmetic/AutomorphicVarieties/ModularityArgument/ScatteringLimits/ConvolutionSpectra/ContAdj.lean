import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

local notation "adj" => ContinuousLinearMap.adjoint

private theorem cnt [TopologicalSpace.SeparableSpace H] {ι : Type} {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (v i) (1 / 2)) (fun i j hij => ?_)
    (fun _ => Metric.isOpen_ball) fun i => Metric.nonempty_ball.2 (by norm_num)
  refine Metric.ball_disjoint_ball ?_
  have h := @norm_sub_sq ℂ H _ _ _ (v i) (v j)
  rw [hv.1, hv.1, hv.2 hij] at h
  simp only [map_zero] at h
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (v i - v j)]

private theorem contAdj {k : ℝ → V →L[ℂ] H} (hk : Continuous k) (c : H) : Continuous fun y => adj (k y) c :=
  (ContinuousLinearMap.adjoint.continuous.comp hk).clm_apply continuous_const

private theorem cSq {k : ℝ → V →L[ℂ] H} (hk : Continuous k) (c : H) : Continuous fun y => ‖adj (k y) c‖ ^ 2 :=
  (contAdj hk c).norm.pow 2

private theorem memL (a b : ℝ) {g : ℝ → V} (hg : Continuous g) : MemLp ((Ioc a b).indicator g) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc a b))
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => hC x (Ioc_subset_Icc_self hx)))

private theorem adjEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (c : H) : adj Y c = J ((memL a b (contAdj hk c)).toLp _) := by
  refine ext_inner_right ℂ fun h => ?_
  obtain ⟨u, rfl⟩ := J.surjective h
  have hu : IntegrableOn (u : ℝ → V) (Ioc a b) := ((Lp.memLp u).restrict _).integrable one_le_two
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hk.continuousOn (s := Icc a b))
  have hi : IntegrableOn (fun y => k y (u y)) (Ioc a b) := by
    refine (hu.norm.const_mul C).mono' ?_ ?_
    · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hk.aestronglyMeasurable.prodMk hu.1)
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
        (k x).le_of_opNorm_le (hC x (Ioc_subset_Icc_self hx)) _)
  rw [ContinuousLinearMap.adjoint_inner_left, hY, ← integral_inner hi, J.inner_map_map, L2.inner_def,
    ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [(memL a b (contAdj hk c)).coeFn_toLp] with x hx
  rw [hx]
  by_cases h : x ∈ Ioc a b <;> simp [h, ContinuousLinearMap.adjoint_inner_left]

private theorem innEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k k' : ℝ → V →L[ℂ] H} {Y Y' : H →L[ℂ] H} (hk : Continuous k) (hk' : Continuous k')
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (hY' : ∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) (c : H) :
    ⟪adj Y c, adj Y' c⟫_ℂ = ∫ y in Ioc a b, ⟪adj (k y) c, adj (k' y) c⟫_ℂ := by
  rw [adjEq J a b hk hY, adjEq J a b hk' hY', J.inner_map_map, L2.inner_def, ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [(memL a b (contAdj hk c)).coeFn_toLp, (memL a b (contAdj hk' c)).coeFn_toLp] with x hx hx'
  rw [hx, hx']
  by_cases h : x ∈ Ioc a b <;> simp [h]

private theorem normEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (c : H) : ‖adj Y c‖ ^ 2 = ∫ y in Ioc a b, ‖adj (k y) c‖ ^ 2 := by
  have h := innEq J a b hk hk hY hY c
  simp only [inner_self_eq_norm_sq_to_K] at h
  have e : ∀ x : ℝ, ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := fun x => by push_cast; rfl
  change ((‖adj Y c‖ : ℝ) : ℂ) ^ 2 = ∫ y in Ioc a b, ((‖adj (k y) c‖ : ℝ) : ℂ) ^ 2 at h
  simp only [e] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

private theorem ptSum {ι : Type} (c : HilbertBasis ι ℂ H) (A A' : V →L[ℂ] H) :
    HasSum (fun m => ⟪adj A (c m), adj A' (c m)⟫_ℂ) (∑ i, ⟪A' (stdOrthonormalBasis ℂ V i), A (stdOrthonormalBasis ℂ V i)⟫_ℂ) := by
  have h := hasSum_sum (s := Finset.univ) fun i _ => c.hasSum_inner_mul_inner (A' (stdOrthonormalBasis ℂ V i)) (A (stdOrthonormalBasis ℂ V i))
  suffices e : ∀ m, ⟪adj A (c m), adj A' (c m)⟫_ℂ = ∑ i, ⟪A' (stdOrthonormalBasis ℂ V i), c m⟫_ℂ * ⟪c m, A (stdOrthonormalBasis ℂ V i)⟫_ℂ by
    simpa only [e] using h
  intro m
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner]
  exact Finset.sum_congr rfl fun i _ => by
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, mul_comm]

private theorem ptSumR {ι : Type} (c : HilbertBasis ι ℂ H) (A : V →L[ℂ] H) :
    HasSum (fun m => ‖adj A (c m)‖ ^ 2) (∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2) := by
  have h := (ptSum c A A).mapL Complex.reCLM
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h

private theorem summ (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) {ι : Type} (c : HilbertBasis ι ℂ H) :
    Summable fun m => ‖adj Y (c m)‖ ^ 2 := by
  have ci : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f (Ioc a b) := fun hf => hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine summable_of_sum_le (c := ∫ y in Ioc a b, ∑ i, ‖k y (stdOrthonormalBasis ℂ V i)‖ ^ 2) (fun _ => sq_nonneg _) fun s => ?_
  simp only [normEq J a b hk hY]
  rw [← integral_finset_sum _ fun m _ => ci (cSq hk _)]
  refine integral_mono (integrable_finset_sum _ fun m _ => ci (cSq hk _))
    (ci (continuous_finset_sum _ fun i _ => (hk.clm_apply continuous_const).norm.pow 2)) fun y => ?_
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) (ptSumR c (k y))

private theorem isHS (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) : IsHilbertSchmidt Y := by
  rw [← isHilbertSchmidt_adjoint_iff, isHilbertSchmidt_iff (stdHilbertBasis ℂ H)]
  have h := summ J a b hk hY (stdHilbertBasis ℂ H)
  have := h.tsum_ofReal_lt_top
  simpa [ENNReal.ofReal_pow] using this

private theorem trEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k k' : ℝ → V →L[ℂ] H} {Y Y' : H →L[ℂ] H} (hk : Continuous k) (hk' : Continuous k')
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (hY' : ∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) :
    trace (adj Y' ∘L Y) = ∫ y in Ioc a b, ∑ i, ⟪k' y (stdOrthonormalBasis ℂ V i), k y (stdOrthonormalBasis ℂ V i)⟫_ℂ := by
  have h1 := isHS J a b hk hY
  have h2 := (isHS J a b hk' hY').adjoint
  let c := stdHilbertBasis ℂ H
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : TopologicalSpace.SeparableSpace H := J.surjective.denseRange.separableSpace J.continuous
  haveI := cnt c.orthonormal
  have s1 := (isTraceClass_comp h1 h2).hasSum_trace c
  have ci : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f (Ioc a b) := fun hf => hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have cg : ∀ m, Continuous fun y => ⟪adj (k y) (c m), adj (k' y) (c m)⟫_ℂ := fun m => (contAdj hk _).inner (contAdj hk' _)
  have s2 := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioc a b))
    (F := fun m y => ⟪adj (k y) (c m), adj (k' y) (c m)⟫_ℂ)
    (fun m => (cg m).integrableOn_Icc.mono_set Ioc_subset_Icc_self) (by
      refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
        ((summ J a b hk hY c).add (summ J a b hk' hY' c))
      rw [normEq J a b hk hY, normEq J a b hk' hY', ← integral_add (ci (cSq hk _)) (ci (cSq hk' _))]
      refine integral_mono (ci (cg m).norm) ((ci (cSq hk _)).add (ci (cSq hk' _))) fun y => ?_
      refine (norm_inner_le_norm _ _).trans ?_
      show _ ≤ ‖adj (k y) (c m)‖ ^ 2 + ‖adj (k' y) (c m)‖ ^ 2
      nlinarith [sq_nonneg (‖adj (k y) (c m)‖ - ‖adj (k' y) (c m)‖), norm_nonneg (adj (k y) (c m)), norm_nonneg (adj (k' y) (c m))])
  simp only [← innEq J a b hk hk' hY hY', (ptSum c _ _).tsum_eq] at s2
  rw [trace_comp_comm_of_isHilbertSchmidt h2 h1]
  refine s1.unique ?_
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left] using s2
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.kp :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) (k k' : ℝ → V →L[ℂ] H) (Y Y' : H →L[ℂ] H), a ≤ b → Continuous k → Continuous k' →
      (∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) → (∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) →
      IsHilbertSchmidt Y ∧ hsNorm Y ^ 2 = ∫ y in a..b, ∑ i, ‖k y (stdOrthonormalBasis ℂ V i)‖ ^ 2 ∧
        trace (ContinuousLinearMap.adjoint Y' ∘L Y) = ∫ y in a..b, ∑ i, ⟪k' y (stdOrthonormalBasis ℂ V i), k y (stdOrthonormalBasis ℂ V i)⟫_ℂ := by
  intro H _ _ _ V _ _ _ _ J a b k k' Y Y' hab hk hk' hY hY'
  have h1 := isHS J a b hk hY
  refine ⟨h1, ?_, by rw [intervalIntegral.integral_of_le hab]; exact trEq J a b hk hk' hY hY'⟩
  have s1 := (isTraceClass_comp h1.adjoint h1).hasSum_trace (stdHilbertBasis ℂ H)
  rw [trEq J a b hk hk hY hY] at s1
  have s2 := Complex.hasSum_ofReal.2 (h1.hasSum_norm_sq (stdHilbertBasis ℂ H))
  have e : ∀ x : H, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, e, ← Complex.ofReal_sum] at s1
  rw [integral_complex_ofReal] at s1
  rw [intervalIntegral.integral_of_le hab]
  exact_mod_cast s2.unique s1
