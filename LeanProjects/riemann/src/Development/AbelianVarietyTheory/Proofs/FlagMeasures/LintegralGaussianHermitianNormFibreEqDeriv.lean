import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHermitianNormFibreDilationStatement
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.GaussFibre

theorem eq_ofReal_deriv (G : ℝ → ℝ≥0∞) (F m : ℝ → ℝ) (β d : ℝ) (hβ : β ≠ 0)
    (hF : HasDerivAt F d β) (hm : ContinuousAt m 1) (hm1 : m 1 = 1)
    (hint : ∀ a b : ℝ, a ≤ b → (0 : ℝ) ∉ Set.Ioc a b →
      ∫⁻ y in Set.Ioc a b, G y = ENNReal.ofReal (F b - F a))
    (hup : ∀ t, 1 ≤ t → G (t * β) ≤ ENNReal.ofReal (m t) * G β)
    (hlo : ∀ t, 0 < t → t ≤ 1 → ENNReal.ofReal (m t) * G β ≤ G (t * β)) :
    G β = ENNReal.ofReal d := by
  have hsl : Tendsto (fun t : ℝ => ENNReal.ofReal (slope F β (t * β))) (𝓝[≠] 1)
      (𝓝 (ENNReal.ofReal d)) := by
    refine (ENNReal.continuous_ofReal.tendsto d).comp
      ((hasDerivAt_iff_tendsto_slope.1 hF).comp ?_)
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t * β) (𝓝 1) (𝓝 (1 * β)) :=
        (continuous_id.mul continuous_const).tendsto 1
      rw [one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht h
      exact ht (mul_right_cancel₀ hβ ((h : t * β = β).trans (one_mul β).symm))
  have hmem : ∀ t y, y ∈ Set.uIoc β (t * β) → ∃ s ∈ Set.uIcc 1 t, s * β = y := by
    intro t y hy
    have h1 := Set.uIoc_subset_uIcc hy
    have h2 := Set.image_mul_const_uIcc β 1 t
    rw [one_mul] at h2
    rw [← h2] at h1
    exact h1
  have hI : ∀ t, 0 < t → t ≠ 1 → ∫⁻ y in Set.uIoc β (t * β), G y =
      ENNReal.ofReal (slope F β (t * β)) * volume (Set.uIoc β (t * β)) := by
    intro t ht ht1
    have h0 : (0 : ℝ) ∉ Set.uIoc β (t * β) := by
      intro h
      obtain ⟨s, hs, hs0⟩ := hmem t 0 h
      have : 0 < s := lt_of_lt_of_le (lt_min one_pos ht) hs.1
      exact (mul_ne_zero this.ne' hβ) hs0
    have hne : t * β - β ≠ 0 := by
      intro h
      exact ht1 (mul_right_cancel₀ hβ ((sub_eq_zero.1 h).trans (one_mul β).symm))
    rw [Real.volume_uIoc, ← ENNReal.ofReal_mul' (abs_nonneg _), slope_def_field]
    rcases le_total β (t * β) with h | h
    · rw [Set.uIoc_of_le h] at h0 ⊢
      rw [hint _ _ h h0, abs_of_nonneg (sub_nonneg.2 h), div_mul_cancel₀ _ hne]
    · rw [Set.uIoc_of_ge h] at h0 ⊢
      rw [hint _ _ h h0, abs_of_nonpos (sub_nonpos.2 h), mul_neg, div_mul_cancel₀ _ hne, neg_sub]
  have hv0 : ∀ t, t ≠ 1 → volume (Set.uIoc β (t * β)) ≠ 0 := by
    intro t ht1
    have hne : t * β - β ≠ 0 := by
      intro h
      exact ht1 (mul_right_cancel₀ hβ ((sub_eq_zero.1 h).trans (one_mul β).symm))
    rw [Real.volume_uIoc]
    exact (ENNReal.ofReal_pos.2 (abs_pos.2 hne)).ne'
  have hvt : ∀ t, volume (Set.uIoc β (t * β)) ≠ ⊤ := by
    intro t
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hev : ∀ p : ℝ → Prop, (∀ᶠ s in 𝓝 (1 : ℝ), p s) →
      ∀ᶠ t in 𝓝 (1 : ℝ), ∀ s ∈ Set.uIcc 1 t, p s := by
    intro p hp
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 hp
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun t ht s hs => h ?_⟩
    rw [Real.dist_eq] at ht ⊢
    exact (Set.abs_sub_left_of_mem_uIcc hs).trans_lt ht
  have hK : ∀ l : Filter ℝ, l ≤ 𝓝 1 →
      Tendsto (fun r : ℝ => ENNReal.ofReal r * G β) l (𝓝 (G β)) := by
    intro l hl
    have := ENNReal.Tendsto.mul_const (b := G β)
      ((ENNReal.continuous_ofReal.tendsto 1).mono_left hl) (Or.inl (by simp))
    simpa using this
  apply le_antisymm
  · refine le_of_tendsto (hK (𝓝[<] 1) nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : r < 1)
    refine ge_of_tendsto (hsl.mono_left (nhdsLT_le_nhdsNE 1)) ?_
    have h1 : ∀ᶠ s in 𝓝 (1 : ℝ), r < m s ∧ 0 < s :=
      (hm.eventually (lt_mem_nhds (hr.trans_eq hm1.symm))).and (lt_mem_nhds one_pos)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hev _ h1)] with t (ht : t < 1) hs
    rw [← ENNReal.mul_le_mul_iff_left (hv0 t ht.ne) (hvt t),
      ← hI t (hs t Set.right_mem_uIcc).2 ht.ne, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_uIoc fun y hy => ?_
    obtain ⟨s, hs', rfl⟩ := hmem t y hy
    refine le_trans ?_ (hlo s (hs s hs').2 (hs'.2.trans (max_le le_rfl ht.le)))
    gcongr
    exact (hs s hs').1.le
  · refine ge_of_tendsto (hK (𝓝[>] 1) nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 1 < r)
    refine le_of_tendsto (hsl.mono_left (nhdsGT_le_nhdsNE 1)) ?_
    have h1 : ∀ᶠ s in 𝓝 (1 : ℝ), m s < r := hm.eventually (gt_mem_nhds (hm1.trans_lt hr))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hev _ h1)] with t (ht : 1 < t) hs
    rw [← ENNReal.mul_le_mul_iff_left (hv0 t ht.ne') (hvt t),
      ← hI t (one_pos.trans ht) ht.ne', ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_uIoc fun y hy => ?_
    obtain ⟨s, hs', rfl⟩ := hmem t y hy
    refine le_trans (hup s ((le_min le_rfl ht.le).trans hs'.1)) ?_
    gcongr
    exact (hs s hs').le

variable {P Q : ℕ}

theorem gaussSp_pos (y : Sp P Q) : 0 < gaussSp y := Real.exp_pos _

theorem integrable_gaussSp : Integrable (gaussSp : Sp P Q → ℝ) := by
  have h1 : Integrable (fun z : ℂ => Real.exp (-‖z‖ ^ 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0).norm
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin P ⊕ Fin Q) (μ := fun _ => (volume : Measure ℂ))
    (f := fun _ (z : ℂ) => Real.exp (-‖z‖ ^ 2)) (fun _ => h1)
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp only [gaussSp, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem gaussSp_smul (c : ℝ) (y : Sp P Q) :
    gaussSp (c • y) = Real.exp (-(c ^ 2 * ∑ i, ‖y i‖ ^ 2)) := by
  simp only [gaussSp, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]

theorem shell {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) (a b : ℝ) (hab : a ≤ b)
    (h0 : (0 : ℝ) ∉ Set.Ioc a b) :
    ∫⁻ t in Set.Ioc a b, ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t) =
      ENNReal.ofReal (2 ^ (P + Q) * (∫ y in {y : Sp P Q | qf y ≤ b}, gaussSp y) -
        2 ^ (P + Q) * ∫ y in {y : Sp P Q | qf y ≤ a}, gaussSp y) := by
  have hq : Measurable (qf : Sp P Q → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  have hO : MeasurableSet {x : Sp P Q | x ≠ 0} := isOpen_ne.measurableSet
  have hg : Measurable fun y : Sp P Q => ENNReal.ofReal (gaussSp y) :=
    ENNReal.measurable_ofReal.comp continuous_gaussSp.measurable
  have key := GlobalTheory.IsFibreFamily_lintegral_preimage hq isOpen_ne subset_rfl h
    (({x : Sp P Q | x ≠ 0}).indicator fun y => ENNReal.ofReal (gaussSp y)) (hg.indicator hO)
    (fun v hv => Set.indicator_of_notMem hv _) (Set.Ioc a b) measurableSet_Ioc
  have hsub : qf ⁻¹' Set.Ioc a b ⊆ {x : Sp P Q | x ≠ 0} := by
    rintro x hx rfl
    apply h0
    simpa [qf] using hx
  rw [Set.indicator_indicator, Set.inter_eq_left.2 hsub,
    lintegral_indicator (hq measurableSet_Ioc), Measure.restrict_restrict (hq measurableSet_Ioc),
    Set.inter_eq_left.2 hsub] at key
  have e0 : ∀ t, ∫⁻ y, ({x : Sp P Q | x ≠ 0}).indicator (fun y => ENNReal.ofReal (gaussSp y)) y
      ∂(fib t) = ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t) := by
    intro t
    have h1 : ∀ᵐ y ∂(fib t), y ∈ qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0} := h.1 t
    apply lintegral_congr_ae
    filter_upwards [h1] with y hy using Set.indicator_of_mem hy.2 _
  simp only [e0] at key
  have e1 : qf ⁻¹' Set.Ioc a b = {x : Sp P Q | qf x ≤ b} \ {x | qf x ≤ a} := by
    ext x; simp [and_comm]
  rw [← key, ← mul_sub, ← integral_diff (s := {x : Sp P Q | qf x ≤ b})
      (t := {x : Sp P Q | qf x ≤ a}) (measurableSet_le hq measurable_const)
      integrable_gaussSp.integrableOn (fun x (hx : qf x ≤ a) => (hx.trans hab : qf x ≤ b)), ← e1,
    ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal integrable_gaussSp.integrableOn
      (Eventually.of_forall fun y => (gaussSp_pos y).le),
    dx, Measure.restrict_smul, lintegral_smul_measure, ENNReal.ofReal_pow (by norm_num)]
  simp

theorem gauss_fibre : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β d : ℝ), IsDxDq fib → β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Sp P Q | qf y ≤ t}, gaussSp y) d β → ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib β) = ENNReal.ofReal (2 ^ (P + Q) * d) := by
  intro P Q fib β d h hβ hF
  have hg : Measurable fun y : Sp P Q => ENNReal.ofReal (gaussSp y) :=
    ENNReal.measurable_ofReal.comp continuous_gaussSp.measurable
  refine eq_ofReal_deriv (fun t => ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib t)) _
    (fun t => t ^ (P + Q) / t) β _ hβ (hF.const_mul (2 ^ (P + Q) : ℝ))
    ((continuousAt_id.pow _).div continuousAt_id one_ne_zero) (by simp)
    (fun a b hab h0 => shell h a b hab h0) (fun t ht => ?_) (fun t ht ht1 => ?_)
  · have ht0 : 0 < t := one_pos.trans_le ht
    rw [GlobalTheory.T.lintegral_hermitianNormFibre_dilation P Q fib β t h hβ ht0 _ hg]
    gcongr with y
    rw [gaussSp_smul, Real.sq_sqrt ht0.le, gaussSp]
    have : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [GlobalTheory.T.lintegral_hermitianNormFibre_dilation P Q fib β t h hβ ht _ hg]
    gcongr with y
    rw [gaussSp_smul, Real.sq_sqrt ht.le, gaussSp]
    have : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
    exact Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory.GaussFibre
