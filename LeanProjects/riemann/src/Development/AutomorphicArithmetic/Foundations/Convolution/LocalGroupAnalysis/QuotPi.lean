import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

open MeasureTheory Topology
open scoped ENNReal

private theorem lintegral_pi_one {ι : Type} [Fintype ι] {T : ι → Type} [∀ i, MeasurableSpace (T i)]
    (ν : ∀ i, Measure (T i)) [∀ i, SigmaFinite (ν i)] (f : ∀ i, T i → NNReal)
    (hf : ∀ i, Measurable (f i)) (h1 : ∀ i, ∫⁻ t, (f i t : ℝ≥0∞) ∂(ν i) = 1) :
    ∫⁻ t, ((∏ i, f i (t i) : NNReal) : ℝ≥0∞) ∂(Measure.pi ν) = 1 := by
  have hint : ∀ i, Integrable (fun t => (f i t : ℝ)) (ν i) := fun i => by
    have := integrable_toReal_of_lintegral_ne_top (μ := ν i) (f := fun t => (f i t : ℝ≥0∞))
      (hf i).coe_nnreal_ennreal.aemeasurable (by rw [h1 i]; exact ENNReal.one_ne_top)
    simpa using this
  have hI : ∀ i, ∫ t, (f i t : ℝ) ∂(ν i) = 1 := fun i => by
    have := lintegral_coe_eq_integral (f i) (hint i)
    rw [h1 i] at this
    exact ENNReal.ofReal_eq_one.1 this.symm
  have hP : Integrable (fun t : ∀ i, T i => ((∏ i, f i (t i) : NNReal) : ℝ)) (Measure.pi ν) := by
    simp only [NNReal.coe_prod]
    exact Integrable.fintype_prod_dep hint
  rw [lintegral_coe_eq_integral _ hP]
  simp only [NNReal.coe_prod]
  rw [integral_fintype_prod_eq_prod (fun i t => (f i t : ℝ))]
  simp [hI]

theorem UpperTheory.ConvolutionTheory.G.quotPi_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotPi := by
  intro hN hE ι _ G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hP J hJ
  haveI : ∀ i, (μ i).IsHaarMeasure := fun i => (hP i).1.1
  haveI : ∀ i, (μ i).IsInvInvariant := fun i => (hP i).1.2
  haveI : ∀ i, (ν i).IsHaarMeasure := fun i => (hP i).2.2.1
  haveI : ∀ i, (ν i).IsInvInvariant := fun i => (hP i).2.2.2
  have hJe : (J : (∀ i, T i) → ∀ i, G i) = Pi.map (fun i => (j i : T i → G i)) := by
    funext t i
    exact hJ t i
  have hPair : UpperTheory.ConvolutionTheory.G.Pair (Measure.pi μ) J (Measure.pi ν) := by
    refine ⟨⟨inferInstance, inferInstance⟩, ?_, ⟨inferInstance, inferInstance⟩⟩
    rw [hJe]
    exact IsClosedEmbedding.piMap fun i => (hP i).2.1
  refine ⟨hPair, fun F hF => ?_⟩
  choose ρ hρc hρn _ using fun i => hN (G i) (T i) (μ i) (j i) (ν i) (hP i)
  have hR : UpperTheory.ConvolutionTheory.G.IsNrm J (Measure.pi ν)
      (fun g => ((∏ i, ρ i (g i) : NNReal) : ℝ≥0∞)) := by
    refine ⟨?_, fun x => ?_⟩
    · exact (Finset.measurable_prod _ fun i _ =>
        (hρc i).measurable.comp (measurable_pi_apply i)).coe_nnreal_ennreal
    · have := lintegral_pi_one ν (fun i t => ρ i (j i t * x i))
        (fun i => ((hρc i).comp ((hP i).2.1.continuous.mul continuous_const)).measurable)
        (fun i => (hρn i).2 (x i))
      simpa only [Pi.mul_apply, hJ] using this
  have hFm : Measurable fun g : ∀ i, G i => ∏ i, F i (g i) :=
    Finset.measurable_prod _ fun i _ => (hF i).1.comp (measurable_pi_apply i)
  have hFi : ∀ t g, (fun g : ∀ i, G i => ∏ i, F i (g i)) (J t * g) =
      (fun g : ∀ i, G i => ∏ i, F i (g i)) g := fun t g => by
    simp only [Pi.mul_apply, hJ, (hF _).2]
  obtain ⟨h1, -, h2⟩ := hE _ _ _ _ _ hPair _ hFm hFi _ hR
  have hloc := fun i => hE (G i) (T i) (μ i) (j i) (ν i) (hP i) (F i) (hF i).1 (hF i).2 _ (hρn i)
  have hfun : (fun x : ∀ i, G i => (∏ i, F i (x i)) *
      ((((∏ i, ρ i (x i) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ)) =
      fun x => ∏ i, (F i (x i) * (((ρ i (x i) : ℝ≥0∞).toReal : ℝ) : ℂ)) := by
    funext x
    simp only [ENNReal.coe_toReal, NNReal.coe_prod, Complex.ofReal_prod, Finset.prod_mul_distrib]
  refine ⟨fun hq => h1.2 ?_, ?_⟩
  · rw [hfun]
    exact Integrable.fintype_prod_dep
      (f := fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ)) fun i => (hloc i).1.1 (hq i)
  · rw [h2, hfun, integral_fintype_prod_eq_prod
      (fun i x => F i x * (((ρ i x : ℝ≥0∞).toReal : ℝ) : ℂ))]
    exact Finset.prod_congr rfl fun i _ => (hloc i).2.2.symm
