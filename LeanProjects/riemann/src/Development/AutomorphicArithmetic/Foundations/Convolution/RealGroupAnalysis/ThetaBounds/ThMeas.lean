import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SummableRationalSchwartz
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem measurable_tsum_complex {ι X : Type} [Countable ι] [MeasurableSpace X] (f : ι → X → ℂ)
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  have hS : MeasurableSet {x | Summable fun i => f i x} := by
    have hm : Measurable fun x => ∑' i, (‖f i x‖₊ : ENNReal) :=
      Measurable.ennreal_tsum fun i => (hf i).nnnorm.coe_nnreal_ennreal
    have : {x | Summable fun i => f i x} = (fun x => ∑' i, (‖f i x‖₊ : ENNReal)) ⁻¹' Set.Iio ⊤ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio, lt_top_iff_ne_top]
      rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
      simp only [coe_nnnorm]
      exact summable_norm_iff.symm
    rw [this]
    exact hm measurableSet_Iio
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι))
    (f := fun s => Set.indicator {x | Summable fun i => f i x} fun x => ∑ i ∈ s, f i x)
    (fun s => (Finset.measurable_sum s fun i _ => hf i).indicator hS) ?_
  rw [tendsto_pi_nhds]
  intro x
  by_cases hx : Summable fun i => f i x
  · have h : Tendsto (fun s : Finset ι => ∑ i ∈ s, f i x) atTop (𝓝 (∑' i, f i x)) := by
      simpa [HasSum] using hx.hasSum
    simpa [Set.indicator, hx] using h
  · simp [Set.indicator, hx, tsum_eq_zero_of_not_summable hx, tendsto_const_nhds]

theorem UpperTheory.ConvolutionTheory.R2.Ff.thMeas :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ThMeas W := by
  intro F E _ _ _ _ _ _ _ D W φ
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hpt : ∀ v, Measurable fun g => (W.Om g φ).1 v := fun v =>
    ((W.cont φ).comp (continuous_id.prodMk continuous_const)).measurable
  have hψ : Continuous (ψ : A F → ℂ) := continuous_subtype_val.comp (continuous_adelicChar (K := F))
  have hhat : ∀ v, Measurable fun g => hat (W.Om g φ).1 v := by
    intro v
    have hc : Continuous fun p : G1 F × A F =>
        (W.Om p.1 φ).1 (Function.update v 1 p.2) * ψ (-(p.2 * v 1)) :=
      ((W.cont φ).comp (continuous_fst.prodMk (continuous_const.update 1 continuous_snd))).mul
        (hψ.comp (continuous_snd.mul continuous_const).neg)
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := adeleMeasure F)).measurable
  refine ⟨?_, ?_, ?_, ?_, hhat⟩
  · exact measurable_tsum_complex _ fun ξ => hpt _
  · intro γ g
    simp only [map_mul, Module.End.mul_apply]
    exact W.th_Om γ _
  · intro r₀ r₁
    exact measurable_tsum_complex _ fun ξ => hhat _
  · intro γ g
    have h := (hatSt F E D W).row γ 0 (W.Om g φ)
    simp only [map_mul, Module.End.mul_apply]
    simpa using h
