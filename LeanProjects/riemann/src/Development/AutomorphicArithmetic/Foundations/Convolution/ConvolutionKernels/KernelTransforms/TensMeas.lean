import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensCont

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem retract_finEmb (h : AdelicGLn.FiniteAdelicGL K n) :
    retractOne (finEmb K n h) = MultiplicityOne.finProj K n h := by
  ext1
  rfl

private theorem retract_pair (a : archGroup K n) (h : AdelicGLn.FiniteAdelicGL K n) :
    retractOne (infFinEquiv K n (a, h)) = archP K n a * MultiplicityOne.finProj K n h := by
  rw [infFinEquiv_apply, retractOne_mul, retract_infEmb, retract_finEmb]

private theorem kbar_retract (κ : archGroup K n → ℂ) (g : AdelicGLn.AdelicGL K n) :
    kbar κ (infPart K n (retractOne g : AdelicGLn.AdelicGL K n)) = kbar κ (infPart K n g) := by
  rw [coe_retractOne, ← map_inv, map_mul]
  exact kbar_mul_zInf κ _ _

private theorem integral_indicator_kbar_shift (hn : 0 < n) {κ : archGroup K n → ℂ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) {Ψ : archGroup K n → ℂ} (hΨ : Continuous Ψ)
    (hΨz : ∀ a s, Ψ (a * zInf K n s) = Ψ a) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (d : {r : ℝ // 0 < r}) :
    ∫ a, GroundTheory.Global.posRealUnitInterval.indicator (fun _ => (1 : ℂ)) (detA K n a * d) * (kbar κ a * Ψ a) ∂ν =
      ∫ a, κ a * Ψ a ∂ν := by
  rw [← integral_indicator_kbar hn hκ hκc hΨ hΨz ν,
    ← integral_mul_left_eq_self
      (fun a => GroundTheory.Global.posRealUnitInterval.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Ψ a)) (zInf K n d)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [zInf_mul_comm, kbar_mul_zInf, hΨz, map_mul, detA_zInf hn]

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Tf.tensMeas :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
      (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ c : ℝ, 0 < c ∧
      ∀ (β : CompactlySupportedContinuousMap (archGroup K n) ℂ) (e : CompactlySupportedContinuousMap (AdelicGLn.FiniteAdelicGL K n) ℂ) (Θ : normOneGL K n → ℂ), Continuous Θ →
        ∫ x : normOneGL K n, kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n)) * Θ x ∂μ =
          c * ∫ a, ∫ h, β a * e h * Θ (archP K n a * MultiplicityOne.finProj K n h) ∂m ∂ν := by
  intro K _ _ n hn μ _ ν _ m _
  have hm : (ν.prod m).IsHaarMeasure := inferInstance
  have hμA : (Measure.map (infFinEquiv K n) (ν.prod m)).IsHaarMeasure :=
    ContinuousMulEquiv.isHaarMeasure_map (ν.prod m) (infFinEquiv K n)
  obtain ⟨c, hc0, hct, hμ⟩ := exists_eq_smul_map_retract hn μ (Measure.map (infFinEquiv K n) (ν.prod m))
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, fun β e Θ hΘ => ?_⟩
  obtain ⟨hF, hFc, -⟩ := UpperTheory.ConvolutionTheory.Tf.tensCont K n hn β e
  have hS : MeasurableSet (detModule K n ⁻¹' GroundTheory.Global.posRealUnitInterval) :=
    continuous_detModule.measurable GroundTheory.Global.measurableSet_posRealUnitInterval
  obtain ⟨Ξ, hΞdef⟩ : ∃ Ξ : normOneGL K n → ℂ, Ξ = fun x : normOneGL K n =>
      kbar β (infPart K n (x : AdelicGLn.AdelicGL K n)) * e (finPart K n (x : AdelicGLn.AdelicGL K n)) * Θ x :=
    ⟨_, rfl⟩
  have hΞ : Continuous Ξ := hΞdef ▸ hF.mul hΘ
  have hΞc : HasCompactSupport Ξ := hΞdef ▸ hFc.mul_right
  have hFm : Measurable ((detModule K n ⁻¹' GroundTheory.Global.posRealUnitInterval).indicator (fun g => Ξ (retractOne g))) :=
    (hΞ.comp continuous_retractOne).measurable.indicator hS
  have hecont : Continuous (infFinEquiv K n) := (infFinEquiv K n).continuous
  have step1 : ∫ x, Ξ x ∂μ = c.toReal • ∫ p, (detModule K n ⁻¹' GroundTheory.Global.posRealUnitInterval).indicator
      (fun g => Ξ (retractOne g)) (infFinEquiv K n p) ∂(ν.prod m) := by
    conv_lhs => rw [hμ]
    rw [integral_smul_measure, integral_map continuous_retractOne.aemeasurable hΞ.aestronglyMeasurable,
      ← integral_indicator hS, integral_map hecont.aemeasurable hFm.aestronglyMeasurable]
  have hint : Integrable (fun p => (detModule K n ⁻¹' GroundTheory.Global.posRealUnitInterval).indicator
      (fun g => Ξ (retractOne g)) (infFinEquiv K n p)) (ν.prod m) := by
    obtain ⟨M, hM⟩ := hΞ.bounded_above_of_compact_support hΞc
    have hC : IsCompact ((infFinEquiv K n) ⁻¹'
        (retractOne ⁻¹' tsupport Ξ ∩ detModule K n ⁻¹' GroundTheory.Global.posRealUnitInterval)) := by
      refine (infFinEquiv K n).toHomeomorph.isCompact_preimage.2 ?_
      rw [← image_mul_centralSection_eq hn]
      exact (hΞc.isCompact.prod isCompact_posRealUnitInterval).image
        ((continuous_subtype_val.comp continuous_fst).mul (continuous_centralSection.comp continuous_snd))
    refine integrable_of_bound_of_compact (hFm.comp hecont.measurable).aestronglyMeasurable
      hC M (fun p _ => (norm_indicator_le_norm_self _ _).trans (hM _)) fun p hp => ?_
    by_contra hne
    have h1 := Set.mem_of_indicator_ne_zero hne
    rw [Set.indicator_of_mem h1] at hne
    exact hp ⟨subset_tsupport _ hne, h1⟩
  have hpt : ∀ (a : archGroup K n) (h : AdelicGLn.FiniteAdelicGL K n),
      (detModule K n ⁻¹' GroundTheory.Global.posRealUnitInterval).indicator (fun g => Ξ (retractOne g)) (infFinEquiv K n (a, h)) =
      GroundTheory.Global.posRealUnitInterval.indicator (fun _ => (1 : ℂ)) (detA K n a * detModule K n (finEmb K n h)) *
        (kbar β a * (e h * Θ (archP K n a * MultiplicityOne.finProj K n h))) := by
    intro a h
    have hd : detModule K n (infFinEquiv K n (a, h)) = detA K n a * detModule K n (finEmb K n h) := by
      rw [infFinEquiv_apply, map_mul]
      rfl
    have hv : Ξ (retractOne (infFinEquiv K n (a, h))) =
        kbar β a * (e h * Θ (archP K n a * MultiplicityOne.finProj K n h)) := by
      rw [hΞdef]
      simp only
      rw [kbar_retract, finPart_retract, retract_pair, infFinEquiv_apply]
      simp only [map_mul, infPart_infEmb, infPart_finEmb, finPart_infEmb, finPart_finEmb, mul_one, one_mul,
        mul_assoc]
    by_cases hI : detA K n a * detModule K n (finEmb K n h) ∈ GroundTheory.Global.posRealUnitInterval
    · rw [Set.indicator_of_mem (by rw [Set.mem_preimage, hd]; exact hI), Set.indicator_of_mem hI, hv, one_mul]
    · rw [Set.indicator_of_notMem (by rw [Set.mem_preimage, hd]; exact hI), Set.indicator_of_notMem hI, zero_mul]
  have hint2 : Integrable (Function.uncurry fun (a : archGroup K n) (h : AdelicGLn.FiniteAdelicGL K n) =>
      β a * e h * Θ (archP K n a * MultiplicityOne.finProj K n h)) (ν.prod m) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((β.continuous.comp continuous_fst).mul (e.continuous.comp continuous_snd)).mul
        (hΘ.comp ((continuous_archP.comp continuous_fst).mul
          (MultiplicityOne.continuous_finProj.comp continuous_snd)))
    · refine HasCompactSupport.intro (β.hasCompactSupport.isCompact.prod e.hasCompactSupport.isCompact) ?_
      rintro ⟨a, h⟩ hp
      by_contra hne
      exact hp ⟨subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul hne)),
        subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul hne))⟩
  rw [← hΞdef, step1, integral_prod_symm _ hint, integral_integral_swap hint2, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [hpt]
  simp only [mul_assoc]
  exact integral_indicator_kbar_shift (κ := β)
    (Ψ := fun a => e h * Θ (archP K n a * MultiplicityOne.finProj K n h)) hn β.continuous β.hasCompactSupport
    (continuous_const.mul (hΘ.comp (continuous_archP.mul continuous_const)))
    (fun a s => by simp only [archimedeanProjection_mul_positiveScalar hn]) ν _
