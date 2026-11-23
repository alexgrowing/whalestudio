import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem map_right_eq_of_CO {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) [m.IsHaarMeasure] {J : Subgroup G} (hJ : CO J) {k : G} (hk : k ∈ J) :
    Measure.map (· * k) m = m := by
  have hcont : Measurable (· * k : G → G) := (continuous_mul_right k).measurable
  haveI : (Measure.map (· * k) m).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right m k
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * k) m) m
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  have hpre : (· * k : G → G) ⁻¹' (J : Set G) = J := by
    ext x
    exact Subgroup.mul_mem_cancel_right J hk
  have h0 : m (J : Set G) ≠ 0 := (hJ.2.measure_pos m ⟨1, J.one_mem⟩).ne'
  have hT : m (J : Set G) ≠ ⊤ := hJ.1.measure_lt_top.ne
  have e := congrArg (fun ν : Measure G => ν (J : Set G)) h
  simp only [Measure.map_apply hcont hmeas, hpre, Measure.smul_apply] at e
  have hc : Measure.haarScalarFactor (Measure.map (· * k) m) m = 1 := by
    have e' : m (J : Set G) = (Measure.haarScalarFactor (Measure.map (· * k) m) m : ENNReal) * m (J : Set G) := by
      simpa [ENNReal.smul_def] using e
    have : ((Measure.haarScalarFactor (Measure.map (· * k) m) m : NNReal) : ENNReal) = 1 :=
      ((ENNReal.mul_eq_right h0 hT).1 e'.symm)
    exact_mod_cast this
  rw [h, hc, one_smul]

theorem UpperTheory.localOperator_comp_rhoL_eq_of_right_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure] (J : Subgroup (Gw n w)), CO J →
          ∀ (φ : Gw n w → ℂ), (∀ k ∈ J, ∀ x, φ (x * k) = φ x) → ∀ T : LL μ →L[ℂ] LL μ, IsOloc μ w mw φ T →
          ∀ k ∈ J, T ∘L rhoL μ w k = T := by
  intro K _ _ n μ _ w _ _ mw _ J hJ φ hφ T hT k hk
  have hmul : ∀ (g : Gw n w) (v : LL μ), rhoL μ w (g * k) v = rhoL μ w g (rhoL μ w k v) := by
    intro g v
    simp only [rhoL, rhoF, map_mul]
    exact UnitaryRep.map_mul_apply _ _ _ v
  have hmp : MeasurePreserving (· * k : Gw n w → Gw n w) mw mw :=
    ⟨(continuous_mul_right k).measurable, map_right_eq_of_CO mw hJ hk⟩
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [ContinuousLinearMap.comp_apply, hT u, hT u v,
    ← hmp.integral_comp (Homeomorph.mulRight k).measurableEmbedding
      (fun g => φ g * ⟪u, rhoL μ w g v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [hφ k hk, hmul]
