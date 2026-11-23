import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LintegralSwapNorm
open PositivityTheory.Rg.Tf.Geo
open MeasureTheory
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.G

section
variable {X T : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
  [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

private theorem lintegral_swap_norm (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsInvInvariant] (i : T →* X) (hi : Continuous i) {a b Ψ : X → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    (hΨ : Measurable Ψ) (hinv : ∀ t x, Ψ (i t * x) = Ψ x) (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1)
    (hB : ∀ x, ∫⁻ t, b (i t * x) ∂ν = 1) :
    ∫⁻ x, Ψ x * a x ∂μ = ∫⁻ x, Ψ x * b x ∂μ :=
  _root_.UpperTheory.Reformulated.B.Qf2.lintegral_swap_norm μ ν i hi ha hb hΨ hinv hA hB

private theorem ae_lt_top_norm (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure]
    (i : T →* X) (hi : Continuous i) {a : X → ℝ≥0∞} (ha : Measurable a) (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1) :
    ∀ᵐ x ∂μ, a x < ⊤ := by
  have him : Measurable i := hi.measurable
  have hS : MeasurableSet (a ⁻¹' {⊤}) := ha (measurableSet_singleton _)
  set c : X → ℝ≥0∞ := (a ⁻¹' {⊤}).indicator 1 with hc
  have hcm : Measurable c := measurable_one.indicator hS
  have hm : Measurable (fun p : X × T => i p.2 * p.1) := (him.comp measurable_snd).mul measurable_fst
  have hu : Measurable (Function.uncurry fun (x : X) (t : T) => c (i t * x)) := hcm.comp hm
  have h0 : ∫⁻ x, ∫⁻ t, c (i t * x) ∂ν ∂μ = 0 := by
    have : ∀ x, ∫⁻ t, c (i t * x) ∂ν = 0 := by
      intro x
      have hf : ∀ᵐ t ∂ν, a (i t * x) < ⊤ :=
        ae_lt_top (ha.comp (him.mul_const x)) (by rw [hA x]; exact ENNReal.one_ne_top)
      have hcx : Measurable (fun t => c (i t * x)) := hcm.comp (him.mul_const x)
      rw [lintegral_eq_zero_iff hcx]
      filter_upwards [hf] with t ht
      simp [hc, ht.ne]
    simp [this]
  have h1 : ∫⁻ x, ∫⁻ t, c (i t * x) ∂ν ∂μ = μ (a ⁻¹' {⊤}) * ν Set.univ := by
    rw [lintegral_lintegral_swap hu.aemeasurable]
    have : ∀ t, ∫⁻ x, c (i t * x) ∂μ = μ (a ⁻¹' {⊤}) := by
      intro t
      rw [lintegral_mul_left_eq_self c (i t), hc, lintegral_indicator_one hS]
    simp [this]
  rw [h1] at h0
  have hν : ν Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne ν)).ne'
  have hμ : μ (a ⁻¹' {⊤}) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hν
  have : ∀ᵐ x ∂μ, x ∉ a ⁻¹' {⊤} := measure_eq_zero_iff_ae_notMem.mp hμ
  filter_upwards [this] with x hx
  exact lt_top_iff_ne_top.mpr hx

private theorem lintegral_ofReal_toReal (μ : Measure X) {a : X → ℝ≥0∞} (hfin : ∀ᵐ x ∂μ, a x < ⊤) (c : X → ℝ) :
    ∫⁻ x, ENNReal.ofReal (c x * (a x).toReal) ∂μ = ∫⁻ x, ENNReal.ofReal (c x) * a x ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with x hx
  rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

private theorem real_eq (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (i : T →* X) (hi : Continuous i) {a b : X → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b)
    (hA : ∀ x, ∫⁻ t, a (i t * x) ∂ν = 1) (hB : ∀ x, ∫⁻ t, b (i t * x) ∂ν = 1) {g : X → ℝ} (hg : Measurable g)
    (hinv : ∀ t x, g (i t * x) = g x) (h1 : Integrable (fun x => g x * (a x).toReal) μ)
    (h2 : Integrable (fun x => g x * (b x).toReal) μ) :
    ∫ x, g x * (a x).toReal ∂μ = ∫ x, g x * (b x).toReal ∂μ := by
  have fa := ae_lt_top_norm μ ν i hi ha hA
  have fb := ae_lt_top_norm μ ν i hi hb hB
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2]
  simp only [← neg_mul]
  rw [lintegral_ofReal_toReal μ fa g, lintegral_ofReal_toReal μ fa (fun x => - g x),
    lintegral_ofReal_toReal μ fb g, lintegral_ofReal_toReal μ fb (fun x => - g x),
    lintegral_swap_norm μ ν i hi ha hb hg.ennreal_ofReal (fun t x => by rw [hinv]) hA hB,
    lintegral_swap_norm μ ν i hi ha hb (Ψ := fun x => ENNReal.ofReal (- g x)) hg.neg.ennreal_ofReal
      (fun t x => by rw [hinv]) hA hB]

private theorem integrable_mul_toReal (μ : Measure X) {Φ : X → ℂ} {a : X → ℝ≥0∞} (hΦ : Measurable Φ)
    (ha : Measurable a) (hf : ∫⁻ x, ‖Φ x‖ₑ * a x ∂μ < ⊤) :
    Integrable (fun x => Φ x * ((a x).toReal : ℂ)) μ := by
  refine ⟨(hΦ.mul (Complex.measurable_ofReal.comp ha.ennreal_toReal)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf
  rw [enorm_mul]
  gcongr
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

end

end UpperTheory.ConvolutionTheory.G

theorem UpperTheory.ConvolutionTheory.G.isUnit_last_join :
    Q1 := by
  intro X G T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ u i hu hi Φ ρ hΦ hinv hn hfin
  have hex : ∃ ρ, IsNormAlong u (fun t => u (i t)) ν ρ := ⟨ρ, hn⟩
  unfold quotInt
  rw [dif_pos hex]
  have h0 := hex.choose_spec
  set ρ₀ := hex.choose
  have ha : Measurable (fun x => ρ (u x)) := hn.1.comp hu
  have hb : Measurable (fun x => ρ₀ (u x)) := h0.1.comp hu
  have hA : ∀ x, ∫⁻ t, ρ (u (i t * x)) ∂ν = 1 := fun x => by simpa [map_mul] using hn.2 x
  have hB : ∀ x, ∫⁻ t, ρ₀ (u (i t * x)) ∂ν = 1 := fun x => by simpa [map_mul] using h0.2 x
  have hfin' : ∫⁻ x, ‖Φ x‖ₑ * ρ₀ (u x) ∂μ < ⊤ := by
    rw [← lintegral_swap_norm μ ν i hi ha hb hΦ.enorm (fun t x => by rw [hinv]) hA hB]
    exact hfin
  have h1 := integrable_mul_toReal μ hΦ ha hfin
  have h2 := integrable_mul_toReal μ hΦ hb hfin'
  have hre : ∀ f : _ → ℂ, Integrable f μ → (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ :=
    fun f hf => (Complex.reCLM.integral_comp_comm hf).symm
  have him : ∀ f : _ → ℂ, Integrable f μ → (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ :=
    fun f hf => (Complex.imCLM.integral_comp_comm hf).symm
  apply Complex.ext
  · rw [hre _ h1, hre _ h2]
    simp only [Complex.re_mul_ofReal]
    refine (real_eq μ ν i hi hb ha hB hA (Complex.measurable_re.comp hΦ) (fun t x => by simp [hinv]) ?_ ?_)
    · simpa [Complex.re_mul_ofReal] using h2.re
    · simpa [Complex.re_mul_ofReal] using h1.re
  · rw [him _ h1, him _ h2]
    simp only [Complex.im_mul_ofReal]
    refine (real_eq μ ν i hi hb ha hB hA (Complex.measurable_im.comp hΦ) (fun t x => by simp [hinv]) ?_ ?_)
    · simpa [Complex.im_mul_ofReal] using h2.im
    · simpa [Complex.im_mul_ofReal] using h1.im
