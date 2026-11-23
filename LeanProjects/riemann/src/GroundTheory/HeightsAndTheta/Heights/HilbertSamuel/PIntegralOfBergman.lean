import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M
open scoped ComplexConjugate InnerProductSpace ENNReal

noncomputable section

namespace IntegralOfBergman

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

lemma continuousOn_source_of_comp {F : Type*} [TopologicalSpace F] (j : Fin A.n) (f : X → F)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source)) :
    ContinuousOn f (A.chart j).source := by
  have h := hf.comp (A.chart j).continuousOn (fun x hx =>
    ⟨(A.chart j).map_source hx, by simpa [Set.mem_preimage, (A.chart j).left_inv hx] using hx⟩)
  refine h.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart j).left_inv hx]

variable {L : HolLineBundle A}

lemma sec_continuousOn {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (j : Fin A.n) :
    ContinuousOn (s j) (A.chart j).source :=
  continuousOn_source_of_comp j (s j) ((hs.1 j j).continuousOn)

lemma weight_continuousOn (W : Weight L) (j : Fin A.n) :
    ContinuousOn (W.φ j) (A.chart j).source :=
  continuousOn_source_of_comp j (W.φ j) ((W.smooth j j).continuousOn)

def ptInner (W : Weight L) (n : ℕ) (s t : Fin A.n → X → ℂ) (x : X) : ℂ :=
  s (chartIdx A x) x * conj (t (chartIdx A x) x) *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ)

lemma ptInner_eq (W : Weight L) {n : ℕ} {s t : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (ht : t ∈ L.sections n) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ptInner W n s t x = s j x * conj (t j x) * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ) := by
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hx' : x ∈ (A.chart (chartIdx A x)).source ∩ (A.chart j).source := ⟨hi, hx⟩
  have hg : L.g (chartIdx A x) j x ≠ 0 := L.ne_zero _ j x hx'
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ‖L.g (chartIdx A x) j x‖ ^ 2 := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hB]; positivity
  have hexp : Real.exp (-(n : ℝ) * (W.φ j x + Real.log B)) =
      Real.exp (-(n : ℝ) * W.φ j x) / B ^ n := by
    rw [show -(n : ℝ) * (W.φ j x + Real.log B) = -(n : ℝ) * W.φ j x - (n : ℝ) * Real.log B by ring,
      Real.exp_sub, ← Real.log_pow, Real.exp_log (pow_pos hBpos n)]
  have hgc : L.g (chartIdx A x) j x * conj (L.g (chartIdx A x) j x) = (B : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hB, Complex.ofReal_pow]
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast hBpos.ne'
  rw [ptInner, (hs.2.1) _ j x hx', (ht.2.1) _ j x hx', W.compat _ j x hx', ← hB, hexp]
  rw [Complex.ofReal_div, Complex.ofReal_pow, map_mul, map_pow]
  calc L.g (chartIdx A x) j x ^ n * s j x *
        ((starRingEnd ℂ) (L.g (chartIdx A x) j x) ^ n * (starRingEnd ℂ) (t j x)) *
        (((Real.exp (-(n : ℝ) * W.φ j x)) : ℂ) / (B : ℂ) ^ n)
      = (L.g (chartIdx A x) j x * conj (L.g (chartIdx A x) j x)) ^ n * (s j x * conj (t j x)) *
        (((Real.exp (-(n : ℝ) * W.φ j x)) : ℂ) / (B : ℂ) ^ n) := by ring
    _ = _ := by rw [hgc]; field_simp

lemma ptInner_self (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    ptInner W n s s x = ((ptNormSq W n s x : ℝ) : ℂ) := by
  rw [ptInner, ptNormSq, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

lemma continuous_ptInner (W : Weight L) {n : ℕ} {s t : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (ht : t ∈ L.sections n) : Continuous (ptInner W n s t) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  set j := chartIdx A x
  have hc : ContinuousOn (fun y => s j y * conj (t j y) *
      ((Real.exp (-(n : ℝ) * W.φ j y) : ℝ) : ℂ)) (A.chart j).source :=
    ((sec_continuousOn hs j).mul (Complex.continuous_conj.comp_continuousOn
      (sec_continuousOn ht j))).mul (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (weight_continuousOn W j))))
  exact (hc.congr (fun y hy => ptInner_eq W hs ht j hy)).continuousAt
    ((A.chart j).open_source.mem_nhds hi)

lemma continuous_ptNormSq (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  have h := Complex.continuous_re.comp (continuous_ptInner W hs hs)
  refine h.congr fun x => ?_
  simp [ptInner_self]

variable [MeasurableSpace X] [BorelSpace X]

lemma measure_pos_of_isOpen (dV : SmoothVolume A) {U : Set X} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < dV.μ U := by
  obtain ⟨x, hxU⟩ := hne
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  set j := chartIdx A x
  set e := A.chart j
  have hU' : IsOpen (e.source ∩ U) := e.open_source.inter hU
  have hWo : IsOpen (e '' (e.source ∩ U)) := e.isOpen_image_source_inter hU
  have hWt : e '' (e.source ∩ U) ⊆ e.target := image_subset_iff.2 fun y hy => e.map_source hy.1
  have hWne : (e '' (e.source ∩ U)).Nonempty := ⟨e x, x, ⟨hi, hxU⟩, rfl⟩
  have key := dV.chart_lintegral j ((e.source ∩ U).indicator 1)
    (measurable_one.indicator hU'.measurableSet)
  have hL : ∫⁻ y in e.source, (e.source ∩ U).indicator 1 y ∂dV.μ ≤ dV.μ U := by
    rw [lintegral_indicator_one hU'.measurableSet, Measure.restrict_apply hU'.measurableSet]
    exact measure_mono (inter_subset_left.trans inter_subset_right)
  have hpos : 0 < ∫⁻ y in e '' (e.source ∩ U), ENNReal.ofReal (dV.dens j y) := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have hmeas : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y))
        (volume.restrict (e '' (e.source ∩ U))) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((dV.smooth j).continuousOn.mono hWt).aemeasurable hWo.measurableSet)
    have hae := (lintegral_eq_zero_iff' hmeas).1 h0
    have hz : volume.restrict (e '' (e.source ∩ U)) = 0 := by
      rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
      filter_upwards [hae, ae_restrict_mem hWo.measurableSet] with y hy hyW
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hy
      exact (not_le.2 (dV.pos j y (hWt hyW))) hy
    rw [Measure.restrict_eq_zero] at hz
    exact (hWo.measure_pos volume hWne).ne' hz
  have hR : ∫⁻ y in e '' (e.source ∩ U), ENNReal.ofReal (dV.dens j y) ≤
      ∫⁻ y in e.target, (e.source ∩ U).indicator 1 (e.symm y) * ENNReal.ofReal (dV.dens j y) := by
    refine le_trans (le_of_eq ?_) (lintegral_mono_set hWt)
    refine setLIntegral_congr_fun hWo.measurableSet fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := hy
    simp [e.left_inv hz.1, hz]
  exact lt_of_lt_of_le hpos (hR.trans (key.symm.le.trans hL))

lemma sectionL2NormSq_pos [CompactSpace X] (W : Weight L) (dV : SmoothVolume A) {n : ℕ}
    {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (h0 : s ≠ 0) : 0 < sectionL2NormSq W dV n s := by
  have := dV.isProb
  have : Measure.IsOpenPosMeasure dV.μ := ⟨fun U hU hne => (measure_pos_of_isOpen dV hU hne).ne'⟩
  obtain ⟨j, hj⟩ : ∃ j, s j ≠ 0 := by
    by_contra! h; exact h0 (funext h)
  obtain ⟨x, hx⟩ : ∃ x, s j x ≠ 0 := by
    by_contra! h; exact hj (funext h)
  have hxs : x ∈ (A.chart j).source := by
    by_contra hn; exact hx (hs.2.2 j x hn)
  have hval : ptNormSq W n s x = ‖s j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) := by
    have h := congrArg Complex.re ((ptInner_self W n s x).symm.trans (ptInner_eq W hs hs j hxs))
    rw [Complex.ofReal_re] at h
    rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpos : ptNormSq W n s x ≠ 0 := by
    rw [hval]; positivity
  exact (continuous_ptNormSq W hs).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (isClosed_tsupport _).isCompact (fun y => by unfold ptNormSq; positivity) hpos

variable [CompactSpace X]

lemma integrable_ptInner (W : Weight L) (dV : SmoothVolume A) {n : ℕ} {s t : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) (ht : t ∈ L.sections n) : Integrable (ptInner W n s t) dV.μ := by
  have := dV.isProb
  exact (continuous_ptInner W hs ht).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

@[instance_reducible]
def l2InnerCore (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ))
    (hV : V ≤ L.sections n) : InnerProductSpace.Core ℂ V where
  inner s t := ∫ x, ptInner W n t s x ∂dV.μ
  conj_inner_symm s t := by
    rw [← integral_conj]
    congr 1
    funext x
    simp only [ptInner, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  re_inner_nonneg s := by
    have h : 0 ≤ ∫ x, ptNormSq W n (s : Fin A.n → X → ℂ) x ∂dV.μ :=
      integral_nonneg fun x => by unfold ptNormSq; positivity
    simp_rw [ptInner_self]
    rw [integral_complex_ofReal]
    simpa using h
  add_left s s' t := by
    rw [← integral_add (integrable_ptInner W dV (hV t.2) (hV s.2))
      (integrable_ptInner W dV (hV t.2) (hV s'.2))]
    congr 1
    funext x
    simp only [ptInner, Submodule.coe_add, Pi.add_apply, map_add]
    ring
  smul_left s t r := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [ptInner, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  definite s h := by
    simp_rw [ptInner_self] at h
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h
    by_contra hne
    have hne' : (s : Fin A.n → X → ℂ) ≠ 0 := by
      simpa using hne
    exact (sectionL2NormSq_pos W dV (hV s.2) hne').ne' h

omit [BorelSpace X] [CompactSpace X] in

lemma integral_ptInner_self (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) :
    ∫ x, ptInner W n s s x ∂dV.μ = ((sectionL2NormSq W dV n s : ℝ) : ℂ) := by
  simp_rw [ptInner_self]
  rw [integral_complex_ofReal, sectionL2NormSq]

lemma iSup_ratio_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (ℓ : E →ₗ[ℂ] ℂ) (w : ℝ) (hw : 0 ≤ w) :
    ⨆ s : E, ‖ℓ s‖ ^ 2 * w / ‖s‖ ^ 2 = (∑ a, ‖ℓ (b a)‖ ^ 2) * w := by
  set S := ∑ a, ‖ℓ (b a)‖ ^ 2 with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun a _ => by positivity
  have hle : ∀ s : E, ‖ℓ s‖ ^ 2 ≤ ‖s‖ ^ 2 * S := by
    intro s
    have hs : ℓ s = ∑ a, ⟪b a, s⟫_ℂ * ℓ (b a) := by
      conv_lhs => rw [← b.sum_repr' s]
      simp [map_sum, map_smul]
    have h1 : ‖ℓ s‖ ≤ ∑ a, ‖⟪b a, s⟫_ℂ‖ * ‖ℓ (b a)‖ := by
      rw [hs]
      exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    have h2 : (∑ a, ‖⟪b a, s⟫_ℂ‖ * ‖ℓ (b a)‖) ^ 2 ≤ (∑ a, ‖⟪b a, s⟫_ℂ‖ ^ 2) * S :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [b.sum_sq_norm_inner_right] at h2
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hbound : ∀ s : E, ‖ℓ s‖ ^ 2 * w / ‖s‖ ^ 2 ≤ S * w := by
    intro s
    rcases eq_or_ne ‖s‖ 0 with h | h
    · simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      positivity
    · rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right (hle s) hw
      nlinarith
  set s0 : E := ∑ a, conj (ℓ (b a)) • b a with hs0
  have hc : ∀ a, ⟪b a, s0⟫_ℂ = conj (ℓ (b a)) := fun a =>
    b.orthonormal.inner_right_fintype (fun a => conj (ℓ (b a))) a
  have hn : ‖s0‖ ^ 2 = S := by
    rw [← b.sum_sq_norm_inner_right]
    simp only [hc, RCLike.norm_conj]
    exact hSdef.symm
  have hl : ℓ s0 = (S : ℂ) := by
    rw [hs0, map_sum, hSdef, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul, Complex.conj_mul', Complex.ofReal_pow]
  apply le_antisymm (ciSup_le hbound)
  refine le_ciSup_of_le ⟨S * w, Set.forall_mem_range.2 hbound⟩ s0 (le_of_eq ?_)
  rw [hl, hn, Complex.norm_real, Real.norm_of_nonneg hS]
  rcases eq_or_ne S 0 with h | h
  · simp [h]
  · field_simp

end IntegralOfBergman

open IntegralOfBergman in

theorem IntegralOfBergman.proof : IntegralOfBergman.Statement := by
  intro D X _ _ _ _ _ A L W dV n V _ hV
  have := dV.isProb
  let ev : X → V →ₗ[ℂ] ℂ := fun x =>
    { toFun := fun s => (s : Fin A.n → X → ℂ) (chartIdx A x) x
      map_add' := fun s t => by simp
      map_smul' := fun r s => by simp }
  let c : InnerProductSpace.Core ℂ V := l2InnerCore W dV n V hV
  let _ : NormedAddCommGroup V := c.toNormedAddCommGroup
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  let b := stdOrthonormalBasis ℂ V
  have hnorm : ∀ s : V, ‖s‖ ^ 2 = sectionL2NormSq W dV n s := fun s => by
    rw [@norm_sq_eq_re_inner ℂ]
    change (∫ x, ptInner W n (s : Fin A.n → X → ℂ) s x ∂dV.μ).re = _
    rw [integral_ptInner_self, Complex.ofReal_re]
  have hpt : ∀ (s : V) (x : X), ptNormSq W n (s : Fin A.n → X → ℂ) x =
      ‖ev x s‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) := fun s x => rfl
  have hB : ∀ x, bergman W dV V n x = ∑ a, ptNormSq W n (b a : Fin A.n → X → ℂ) x := by
    intro x
    rw [bergman]
    simp_rw [hpt, ← hnorm]
    rw [iSup_ratio_eq b (ev x) _ (Real.exp_pos _).le, Finset.sum_mul]
  simp_rw [hB]
  rw [integral_finsetSum _ fun a _ => (continuous_ptNormSq W (hV (b a).2)).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact]
  have h1 : ∀ a, ∫ x, ptNormSq W n (b a : Fin A.n → X → ℂ) x ∂dV.μ = 1 := fun a => by
    rw [← sectionL2NormSq, ← hnorm, b.orthonormal.1 a, one_pow]
  simp_rw [h1]
  simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
