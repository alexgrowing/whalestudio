import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.UnipMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtClosed

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

private theorem p0_mem {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {J : L V →ₗᵢ[ℂ] H} {J' : L W →ₗᵢ[ℂ] H} {P : H →L[ℂ] H} (hP : IsOrthogonalProjectionTwoLines J J' P) (S : Submodule ℂ H)
    (hS : IsClosed (S : Set H)) (h₁ : ∀ u, J u ∈ S) (h₂ : ∀ v, J' v ∈ S) (φ : H) : P φ ∈ S := by
  haveI : CompleteSpace S := hS.completeSpace_coe
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro w hw
  have h0 : P w = 0 := (hP.2.2 w).2
    ⟨fun u => Submodule.inner_right_of_mem_orthogonal (h₁ u) hw, fun v => Submodule.inner_right_of_mem_orthogonal (h₂ v) hw⟩
  have h := hP.1.isSymmetric w φ
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h, h0, inner_zero_left]

private theorem ct_rc_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (f : CC K n) (φ : L2 μ) (r : ℕ) (hφ : constantTermL2 μ r φ =ᵐ[μ] 0) (x : G1 K n) : ct r (rc μ f φ) x = 0 := by
  change ∫ X in unipFundamentalDomain K n r, rconv (rationalGLOne K n) μ f φ (unipOne K n r X * x)
      ∂unipMeasure K n r = 0
  haveI : SigmaCompactSpace (normOneGL K n) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SFinite μ := instSFiniteOfSigmaFinite
  set S := (x * ·) '' tsupport (f : normOneGL K n → ℂ)
  have hS : IsCompact S := f.hasCompactSupport.isCompact.image (continuous_const_mul x)
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hfS : ∀ z ∉ S, f (x⁻¹ * z) = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz ⟨x⁻¹ * z, h, by simp⟩
  set F : (UPos n r → 𝔸[K]) → normOneGL K n → ℂ :=
    fun X z => f (x⁻¹ * z) * φ (mk (rationalGLOne K n) (unipOne K n r X * z))
  have hFm : StronglyMeasurable (Function.uncurry F) :=
    (f.continuous.comp (continuous_const_mul x⁻¹ |>.comp continuous_snd)).stronglyMeasurable.mul
      ((Lp.stronglyMeasurable φ).comp_measurable ((measurable_mk (rationalGLOne K n)).comp
        (continuous_unipOne_mul r).measurable))
  have hint : Integrable (Function.uncurry F)
      (((unipMeasure K n r).restrict (unipFundamentalDomain K n r)).prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    obtain ⟨C, hC, hCφ⟩ := exists_lintegral_unip_sq_le μ r hS
    have hfin : ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
        ‖φ (mk (rationalGLOne K n) (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ < ⊤ :=
      L2Kernel.lt_top_of_sq_lt_top ((hCφ φ).trans_lt
        (ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_lt_top enorm_lt_top)))
    have hmeas : Measurable fun p : (UPos n r → 𝔸[K]) × normOneGL K n =>
        ‖φ (mk (rationalGLOne K n) (unipOne K n r p.1 * p.2))‖ₑ :=
      ((Lp.stronglyMeasurable φ).measurable.comp ((measurable_mk (rationalGLOne K n)).comp
        (continuous_unipOne_mul r).measurable)).enorm
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.aestronglyMeasurable.enorm]
    calc ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z, ‖Function.uncurry F (X, z)‖ₑ ∂μ ∂unipMeasure K n r
        ≤ ∫⁻ X in unipFundamentalDomain K n r, ∫⁻ z in S,
            ENNReal.ofReal M * ‖φ (mk (rationalGLOne K n) (unipOne K n r X * z))‖ₑ ∂μ ∂unipMeasure K n r := by
          refine lintegral_mono fun X => ?_
          rw [← lintegral_indicator hS.measurableSet]
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ S
          · rw [indicator_of_mem hz]
            simp only [F, Function.uncurry_apply_pair, enorm_mul]
            gcongr
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hM _)
          · rw [indicator_of_notMem hz]
            simp [F, hfS z hz]
      _ = ENNReal.ofReal M * ∫⁻ z in S, ∫⁻ X in unipFundamentalDomain K n r,
            ‖φ (mk (rationalGLOne K n) (unipOne K n r X * z))‖ₑ ∂unipMeasure K n r ∂μ := by
          simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_lintegral_swap hmeas.aemeasurable
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hinner : ∀ X, rconv (rationalGLOne K n) μ f φ (unipOne K n r X * x) = ∫ z, F X z ∂μ := by
    intro X
    rw [rconv, ← integral_mul_left_eq_self _ (unipOne K n r X)]
    congr 1
    ext z
    simp only [F, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hCT : ∀ z, ∫ X in unipFundamentalDomain K n r, F X z ∂unipMeasure K n r =
      f (x⁻¹ * z) * constantTermL2 μ r φ z := by
    intro z
    simp only [F, constantTermL2, ctFun]
    exact integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_integral_swap hint]
  simp_rw [hCT]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hφ] with z hz
  rw [hz, Pi.zero_apply, mul_zero]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctVanish :
    ForAllC fun K _ _ μ _ _ _ _ _ _ _ _ A A' => ∀ (a : CC K (2 + 2)) (P : L2 μ →L[ℂ] L2 μ), IsOrthogonalProjectionTwoLines A.J A'.J P → (∀ φ, P φ = φ → ∀ z, ct 1 (rc μ a φ) z = 0 ∧ ct 3 (rc μ a φ) z = 0) ∧
      Pc μ ∘L P = 0 ∧ P ∘L Pc μ = 0 := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' a P hP
  have hp' : Pair μ₂ τ₂ τ₁ := ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩
  have h₁ := ctZero K μ μ₂ τ₁ τ₂ hp D d d' A A'
  have h₂ := ctZero K μ μ₂ τ₂ τ₁ hp' D d' d A' A
  refine ⟨fun φ hφ z => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨S, hS, hm⟩ := ctClosed μ 1
    refine ct_rc_zero μ a φ 1 ((hm φ).1 ?_) z
    rw [← hφ]
    exact p0_mem hP S hS (fun u => (hm _).2 (h₁ u).2.2.1) (fun u => (hm _).2 (h₂ u).2.2.1) φ
  · obtain ⟨S, hS, hm⟩ := ctClosed μ 3
    refine ct_rc_zero μ a φ 3 ((hm φ).1 ?_) z
    rw [← hφ]
    exact p0_mem hP S hS (fun u => (hm _).2 (h₁ u).2.2.2) (fun u => (hm _).2 (h₂ u).2.2.2) φ
  · refine ContinuousLinearMap.ext fun φ => ?_
    exact p0_mem hP (Pc μ).ker (Pc μ).isClosed_ker (fun u => (h₁ u).1) (fun u => (h₂ u).1) φ
  · refine ContinuousLinearMap.ext fun φ => ?_
    have hs : ∀ w, ⟪w, Pc μ φ⟫_ℂ = ⟪Pc μ w, φ⟫_ℂ := fun w => by
      unfold Pc
      exact (Submodule.inner_starProjection_left_eq_right _ w φ).symm
    refine (hP.2.2 (Pc μ φ)).2 ⟨fun u => ?_, fun v => ?_⟩
    · rw [hs, (h₁ u).1, inner_zero_left]
    · rw [hs, (h₂ v).1, inner_zero_left]
