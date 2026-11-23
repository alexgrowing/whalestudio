import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.HilbertLemmas

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

section helpers

variable {M : Type*} [TopologicalSpace M]

theorem gm_cont_of_smoothR (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) : Continuous ph := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => congrFun he y
  have h := (hph e hc).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have h2 := h.comp (e.continuousAt hx)
  have h3 : ContinuousAt (fun y => (ph y : ℂ)) x := by
    refine h2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  simpa [Function.comp_def] using Complex.continuous_re.continuousAt.comp h3

private lemma natCast_le_coe_infty (k : ℕ) : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  first
    | exact WithTop.coe_le_coe.2 le_top
    | exact_mod_cast le_top
    | (norm_cast; exact le_top)
    | simp

theorem gm_exp_ck (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph) (s : ℝ) (k : ℕ) :
    Ck n z k (fun y => (Real.exp (s * ph y) : ℂ)) := by
  intro e he
  have h := hph e he
  have hre : ContDiffOn ℝ ∞ (fun w => ph (e.symm w)) e.target := by
    have := Complex.reCLM.contDiff.comp_contDiffOn h
    simpa [Function.comp_def] using this
  have hmul : ContDiffOn ℝ ∞ (fun w => s * ph (e.symm w)) e.target := contDiffOn_const.mul hre
  have hrexp : ContDiffOn ℝ ∞ (fun w => Real.exp (s * ph (e.symm w))) e.target :=
    Real.contDiff_exp.comp_contDiffOn hmul
  have hexp : ContDiffOn ℝ ∞ (fun w => (Real.exp (s * ph (e.symm w)) : ℂ)) e.target := by
    have := Complex.ofRealCLM.contDiff.comp_contDiffOn hrexp
    simpa [Function.comp_def] using this
  exact hexp.of_le (natCast_le_coe_infty k)

theorem gm_form_continuous {n : ℕ} (f : M → V n) (hf : ∀ k, Continuous fun x => f x k) :
    Continuous f := by
  first
    | exact continuous_pi hf
    | exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hf)
    | (have h1 : Continuous (fun x => WithLp.ofLp (f x)) := continuous_pi hf
       simpa using (PiLp.continuous_toLp 2 _).comp h1)
    | fun_prop

theorem gm_form_hcs {n : ℕ} (f : M → V n) (hf : ∀ k, HasCompactSupport (fun x => f x k)) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro' (K := ⋃ k, tsupport (fun x => f x k))
    (isCompact_iUnion fun k => hf k) (isClosed_iUnion_of_finite fun k => isClosed_tsupport _) ?_
  intro x hx
  simp only [mem_iUnion, not_exists] at hx
  ext k
  first
    | simpa using image_eq_zero_of_notMem_tsupport (hx k)
    | simpa using image_eq_zero_of_nmem_tsupport (hx k)

end helpers

section forms

variable {M : Type*} [TopologicalSpace M]

def gmTestForms (n : ℕ) (z : M → V n) : Submodule ℂ (M → V n) where
  carrier := {f | IsTestForm n z f}
  add_mem' := by
    intro f g hf hg k
    refine ⟨?_, ?_⟩
    · have := Ck.add n z 2 _ _ (hf k).1 (hg k).1
      simpa using this
    · have e : (fun x => (f + g) x k) = (fun x => f x k) + (fun x => g x k) := by
        funext x; simp
      rw [e]; exact (hf k).2.add (hg k).2
  zero_mem' := by
    intro k
    refine ⟨?_, ?_⟩
    · simpa using Ck.const n z 2 0
    · have e : (fun x => (0 : M → V n) x k) = 0 := by
        funext x; simp
      rw [e]; exact HasCompactSupport.zero
  smul_mem' := by
    intro c f hf k
    refine ⟨?_, ?_⟩
    · have := Ck.mul n z 2 _ _ (Ck.const n z 2 c) (hf k).1
      simpa using this
    · have e : (fun x => (c • f) x k) = (fun _ => c) * (fun x => f x k) := by
        funext x; simp
      rw [e]; exact HasCompactSupport.mul_left (hf k).2

private lemma continuous_d_of_ck_two {n : ℕ} {z : M → V n} (hz : IsLocalHomeomorph z) {g : M → ℂ}
    (hg : Ck n z 2 g) (j : Fin n) : Continuous (d n z j g) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨e0, hx0, he0⟩ := hz x0
  have hc0 : IsChart n z e0 := fun y _ => congrFun he0 y
  have hloc : ∀ x ∈ e0.source, d n z j g x = wd n j (g ∘ e0.symm) (z x) := by
    intro x hx
    unfold d
    have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e0, hc0, hx⟩
    rw [dif_pos hex]
    set e := Classical.choose hex with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec hex
    have hzx : z x = e x := he.1 he.2
    have hT : Tendsto e.symm (𝓝 (z x)) (𝓝 x) := by
      have := (e.continuousAt_symm (e.map_source he.2)).tendsto
      rwa [e.left_inv he.2, ← hzx] at this
    have hev : (g ∘ e.symm) =ᶠ[𝓝 (z x)] (g ∘ e0.symm) := by
      have h1 : ∀ᶠ w in 𝓝 (z x), e.symm w ∈ e0.source := hT.eventually (e0.open_source.mem_nhds hx)
      have h2 : ∀ᶠ w in 𝓝 (z x), w ∈ e.target := by
        rw [hzx]
        exact e.open_target.mem_nhds (e.map_source he.2)
      filter_upwards [h1, h2] with w hw1 hw2
      have h3 : z (e.symm w) = w := by
        rw [he.1 (e.map_target hw2), e.right_inv hw2]
      have h4 : e0 (e.symm w) = w := by
        rw [← hc0 hw1, h3]
      have h5 : e.symm w = e0.symm w :=
        calc e.symm w = e0.symm (e0 (e.symm w)) := (e0.left_inv hw1).symm
          _ = e0.symm w := by rw [h4]
      simp only [Function.comp_apply, h5]
    unfold wd
    rw [hev.fderiv_eq (𝕜 := ℝ)]
  have hcont : ContinuousAt (fun x => wd n j (g ∘ e0.symm) (z x)) x0 := by
    have hG : ContinuousOn (fun y => fderiv ℝ (g ∘ e0.symm) y) e0.target := by
      first
        | exact (hg e0 hc0).continuousOn_fderiv_of_isOpen e0.open_target (by norm_num)
        | exact (hg e0 hc0).continuousOn_fderiv_of_isOpen e0.open_target (by simp)
    have hzc : ContinuousAt z x0 := by
      rw [he0]
      exact e0.continuousAt hx0
    have hmem : z x0 ∈ e0.target := by
      rw [he0]
      exact e0.map_source hx0
    have hGz : ContinuousAt (fun x => fderiv ℝ (g ∘ e0.symm) (z x)) x0 :=
      (hG.continuousAt (e0.open_target.mem_nhds hmem)).comp hzc
    unfold wd
    have hb1 := hGz.clm_apply (continuousAt_const : ContinuousAt (fun _ : M => bas n j) x0)
    have hb2 := hGz.clm_apply
      (continuousAt_const : ContinuousAt (fun _ : M => Complex.I • bas n j) x0)
    exact (hb1.sub (continuousAt_const.mul hb2)).div_const 2
  refine hcont.congr ?_
  filter_upwards [e0.open_source.mem_nhds hx0] with x hx
  exact (hloc x hx).symm

theorem gm_tstar_cont (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (f : M → V n) (hf : IsTestForm n z f) :
    Continuous (tstar n z ph ph f) := by
  have hE1 : Ck n z 2 (fun y => (Real.exp (-ph y) : ℂ)) := by
    simpa [neg_one_mul] using gm_exp_ck n z ph hph (-1) 2
  have hph' := gm_cont_of_smoothR n z hz ph hph
  have hsum : Continuous (fun x => ∑ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x) :=
    continuous_finset_sum _ fun j _ => continuous_d_of_ck_two hz (Ck.mul n z 2 _ _ hE1 (hf j).1) j
  have hE : Continuous (fun x => (Real.exp (ph x) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp hph')
  exact (hE.mul hsum).neg

private lemma d_eq_zero_of_not_mem_tsupport {n : ℕ} {z : M → V n} {g : M → ℂ} {x : M} (j : Fin n)
    (hx : x ∉ tsupport g) : d n z j g x = 0 := by
  unfold d
  split_ifs with h
  · set e := Classical.choose h with he_def
    have he : IsChart n z e ∧ x ∈ e.source := Classical.choose_spec h
    have hU : g =ᶠ[𝓝 x] 0 := by
      first
        | exact notMem_tsupport_iff_eventuallyEq.1 hx
        | exact not_mem_tsupport_iff_eventuallyEq.1 hx
    have hT : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have := (e.continuousAt_symm (e.map_source he.2)).tendsto
      rwa [e.left_inv he.2] at this
    have hev : (g ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => 0 := by
      rw [he.1 he.2]
      exact hT.eventually hU
    have hfd : fderiv ℝ (g ∘ e.symm) (z x) = 0 := by
      rw [hev.fderiv_eq]
      exact fderiv_const_apply _
    simp only [wd, hfd, ContinuousLinearMap.zero_apply, mul_zero, sub_zero, zero_div]
  · rfl

theorem gm_tstar_hcs (n : ℕ) (z : M → V n) (ph : M → ℝ) (f : M → V n) (hf : IsTestForm n z f) :
    HasCompactSupport (tstar n z ph ph f) := by
  refine HasCompactSupport.intro' (K := ⋃ k, tsupport (fun x => f x k))
    (isCompact_iUnion fun k => (hf k).2) (isClosed_iUnion_of_finite fun k => isClosed_tsupport _) ?_
  intro x hx
  simp only [mem_iUnion, not_exists] at hx
  have hzero : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x = 0 := by
    intro j
    apply d_eq_zero_of_not_mem_tsupport
    intro hmem
    have hsub : Function.support (fun y => (Real.exp (-ph y) : ℂ) * f y j) ⊆
        Function.support (fun y => f y j) := fun y hy hy0 => hy (by simp [hy0])
    exact hx j (closure_mono hsub hmem)
  simp only [tstar]
  rw [Finset.sum_eq_zero (fun j _ => hzero j)]
  simp

private lemma ck_one_of_ck_two {n : ℕ} {z : M → V n} {f : M → ℂ} (h : Ck n z 2 f) : Ck n z 1 f := by
  intro e he
  refine (h e he).of_le ?_
  first
    | norm_num
    | exact_mod_cast (show (1 : ℕ) ≤ 2 by norm_num)
    | exact WithTop.coe_le_coe.2 (by norm_num)

theorem gm_tstar_add (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph)
    (f g : M → V n) (hf : IsTestForm n z f) (hg : IsTestForm n z g) (x : M) :
    tstar n z ph ph (f + g) x = tstar n z ph ph f x + tstar n z ph ph g x := by
  have hE : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ)) := by
    simpa [neg_one_mul] using gm_exp_ck n z ph hph (-1) 1
  have key : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * (f + g) y j) x =
      d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x +
        d n z j (fun y => (Real.exp (-ph y) : ℂ) * g y j) x := by
    intro j
    have hf1 : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ) * f y j) :=
      Ck.mul n z 1 _ _ hE (ck_one_of_ck_two (hf j).1)
    have hg1 : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ) * g y j) :=
      Ck.mul n z 1 _ _ hE (ck_one_of_ck_two (hg j).1)
    rw [← d_add n z _ _ hf1 hg1 j x]
    congr 1
    funext y
    simp [mul_add]
  simp only [tstar, key, Finset.sum_add_distrib]
  ring

theorem gm_tstar_smul (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph)
    (c : ℂ) (f : M → V n) (hf : IsTestForm n z f) (x : M) :
    tstar n z ph ph (c • f) x = c * tstar n z ph ph f x := by
  have hE : Ck n z 1 (fun y => (Real.exp (-ph y) : ℂ)) := by
    simpa [neg_one_mul] using gm_exp_ck n z ph hph (-1) 1
  have key : ∀ j, d n z j (fun y => (Real.exp (-ph y) : ℂ) * (c • f) y j) x =
      c * d n z j (fun y => (Real.exp (-ph y) : ℂ) * f y j) x := by
    intro j
    rw [← d_const_mul n z c _ (Ck.mul n z 1 _ _ hE (ck_one_of_ck_two (hf j).1)) j x]
    congr 1
    funext y
    first
      | simp [mul_left_comm]
      | (simp <;> ring)
  simp only [tstar, key, ← Finset.mul_sum]
  ring

end forms

section meas

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

theorem gm_lintegral_wvol {E : Type*} [NormedAddCommGroup E] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : Measurable ph) (g : M → E) :
    ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂wvol n z ph =
      ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ph x)) ∂vol n z := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-ph x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph.neg)
  rw [wvol, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [Pi.mul_apply, ← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

theorem gm_memLp_two_iff {E : Type*} [NormedAddCommGroup E] {μ : Measure M} (g : M → E)
    (hg : AEStronglyMeasurable g μ) :
    MemLp g 2 μ ↔ ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) ∂μ < ⊤ := by
  first
    | (simp only [MemLp, hg, true_and]
       rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
       simp)
    | (rw [MemLp, and_iff_right hg, eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
       simp only [ENNReal.toReal_ofNat]
       rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)])

theorem gm_norm_sq {E : Type*} [NormedAddCommGroup E] {μ : Measure M} (u : Lp E 2 μ) :
    ENNReal.ofReal (‖u‖ ^ 2) = ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂μ := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u),
    eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

theorem gm_integral_wvol (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : Measurable ph)
    (G : M → ℂ) :
    ∫ x, G x ∂wvol n z ph = ∫ x, (Real.exp (-ph x) : ℂ) * G x ∂vol n z ∧
      (Integrable G (wvol n z ph) → Integrable (fun x => (Real.exp (-ph x) : ℂ) * G x) (vol n z)) := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-ph x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph.neg)
  have hlt : ∀ᵐ x ∂vol n z, ENNReal.ofReal (Real.exp (-ph x)) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hfun : (fun x => (ENNReal.ofReal (Real.exp (-ph x))).toReal • G x) =
      fun x => (Real.exp (-ph x) : ℂ) * G x := by
    funext x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  refine ⟨?_, fun h => ?_⟩
  · rw [wvol, integral_withDensity_eq_integral_toReal_smul hm hlt, hfun]
  · rw [wvol, integrable_withDensity_iff_integrable_smul' hm hlt, hfun] at h
    exact h

theorem gm_inner_toLp (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : Measurable ph)
    (u : Lp ℂ 2 (wvol n z ph)) (g : M → ℂ) (hg : MemLp g 2 (wvol n z ph)) :
    ⟪u, hg.toLp g⟫_ℂ = ∫ x, (Real.exp (-ph x) : ℂ) * (conj (u x) * g x) ∂vol n z ∧
      Integrable (fun x => (Real.exp (-ph x) : ℂ) * (conj (u x) * g x)) (vol n z) := by
  have hpt : ∀ x, ⟪u x, g x⟫_ℂ = conj (u x) * g x := by
    intro x
    first
      | exact RCLike.inner_apply _ _
      | (simp [RCLike.inner_apply]; ring)
      | (simp; ring)
  have hint : Integrable (fun x => conj (u x) * g x) (wvol n z ph) := by
    refine (L2.integrable_inner (𝕜 := ℂ) u (hg.toLp g)).congr ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, hpt]
  have hinner : ⟪u, hg.toLp g⟫_ℂ = ∫ x, conj (u x) * g x ∂wvol n z ph := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, hpt]
  obtain ⟨h1, h2⟩ := gm_integral_wvol n z ph hph (fun x => conj (u x) * g x)
  exact ⟨hinner.trans h1, h2 hint⟩

end meas

section maps

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem gm_hcs_of {E F : Type*} [Zero E] [Zero F] (t : M → E) (G : M → F) (ht : HasCompactSupport t)
    (h : ∀ x, t x = 0 → G x = 0) : HasCompactSupport G := by
  first
    | exact ht.mono fun x hx h0 => hx (h x h0)
    | exact ht.mono' (closure_mono fun x hx h0 => hx (h x h0))

theorem gm_memLp_tstar (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (f : M → V n) (hf : IsTestForm n z f) :
    MemLp (tstar n z ph ph f) 2 (wvol n z ph) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hc : Continuous (tstar n z ph ph f) := gm_tstar_cont n z hz ph hph f hf
  have hs := gm_tstar_hcs n z ph f hf
  have hph' := gm_cont_of_smoothR n z hz ph hph
  rw [gm_memLp_two_iff _ hc.aestronglyMeasurable, gm_lintegral_wvol n z ph hph'.measurable]
  have hG : Continuous (fun x => ‖tstar n z ph ph f x‖ ^ 2 * Real.exp (-ph x)) :=
    (hc.norm.pow 2).mul (Real.continuous_exp.comp hph'.neg)
  have hGs : HasCompactSupport (fun x => ‖tstar n z ph ph f x‖ ^ 2 * Real.exp (-ph x)) :=
    gm_hcs_of _ _ hs fun x hx => by simp [hx]
  exact (hG.integrable_of_hasCompactSupport hGs (μ := vol n z)).lintegral_lt_top

private lemma continuous_of_ck {n : ℕ} {z : M → V n} (hz : IsLocalHomeomorph z) {k : ℕ} {g : M → ℂ}
    (hg : Ck n z k g) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => congrFun he y
  have h := (hg e hc).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have h2 := h.comp (e.continuousAt hx)
  refine h2.congr ?_
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp [e.left_inv hy]

theorem gm_ipV_integrable (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (v : M → V n) (hv : Continuous v) (f : M → V n)
    (hf : IsTestForm n z f) :
    Integrable (fun x => ⟪v x, f x⟫_ℂ * (Real.exp (-ph x) : ℂ)) (vol n z) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hfc : Continuous f := gm_form_continuous f fun k => continuous_of_ck hz (hf k).1
  have hfs : HasCompactSupport f := gm_form_hcs f fun k => (hf k).2
  have hph' : Continuous ph := gm_cont_of_smoothR n z hz ph hph
  have hcont : Continuous (fun x => ⟪v x, f x⟫_ℂ * (Real.exp (-ph x) : ℂ)) := by
    have h1 : Continuous (fun x => ⟪v x, f x⟫_ℂ) := hv.inner hfc
    have h2 : Continuous (fun x => (Real.exp (-ph x) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp hph'.neg)
    exact h1.mul h2
  exact hcont.integrable_of_hasCompactSupport (gm_hcs_of f _ hfs fun x hx => by simp [hx])

theorem gm_ipV_add (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (v : M → V n) (hv : Continuous v) (f g : M → V n)
    (hf : IsTestForm n z f) (hg : IsTestForm n z g) :
    ipV n z v (f + g) ph = ipV n z v f ph + ipV n z v g ph := by
  have h1 := gm_ipV_integrable n z hz ph hph v hv f hf
  have h2 := gm_ipV_integrable n z hz ph hph v hv g hg
  simp only [ipV, Pi.add_apply, inner_add_right, add_mul]
  exact integral_add h1 h2

theorem gm_ipV_smul (n : ℕ) (z : M → V n) (ph : M → ℝ) (v : M → V n) (c : ℂ) (f : M → V n) :
    ipV n z v (c • f) ph = c * ipV n z v f ph := by
  simp only [ipV, Pi.smul_apply, inner_smul_right, mul_assoc]
  first
    | exact integral_const_mul c _
    | exact integral_mul_left c _

def gmTheta (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) : gmTestForms n z →ₗ[ℂ] Lp ℂ 2 (wvol n z ph) where
  toFun f := (gm_memLp_tstar n z hz ph hph f f.2).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _
      (Eventually.of_forall fun x => gm_tstar_add n z ph hph f g f.2 g.2 x)
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => gm_tstar_smul n z ph hph c f f.2 x)

def gmEll (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (v : M → V n) (hv : Continuous v) : gmTestForms n z →ₗ[ℂ] ℂ where
  toFun f := ipV n z v f ph
  map_add' f g := gm_ipV_add n z hz ph hph v hv f g f.2 g.2
  map_smul' c f := by
    rw [RingHom.id_apply, smul_eq_mul]
    exact gm_ipV_smul n z ph v c f

def gmSingle {n : ℕ} (ph : M → ℝ) (φ : M → ℂ) (j : Fin n) : M → V n :=
  fun y => EuclideanSpace.single j ((Real.exp (ph y) : ℂ) * conj (φ y))

theorem gm_single_isTestForm (n : ℕ) (z : M → V n) (ph : M → ℝ) (hph : SmoothR n z ph)
    (φ : M → ℂ) (hφ : IsTest n z φ) (j : Fin n) : IsTestForm n z (gmSingle ph φ j) := by
  intro k
  have hE : Ck n z 2 (fun y => (Real.exp (ph y) : ℂ)) := by
    simpa using gm_exp_ck n z ph hph 1 2
  have hc : Ck n z 2 (fun y => conj (φ y)) := by
    intro e he
    have h := (hφ.1 e he).of_le (natCast_le_coe_infty 2)
    have := Complex.conjCLE.contDiff.comp_contDiffOn h
    simpa [Function.comp_def] using this
  by_cases hk : k = j
  · subst hk
    refine ⟨?_, ?_⟩
    · simpa [gmSingle] using Ck.mul n z 2 _ _ hE hc
    · exact gm_hcs_of _ _ hφ.2 fun x hx => by simp [gmSingle, hx]
  · refine ⟨?_, ?_⟩
    · simpa [gmSingle, hk] using Ck.const n z 2 0
    · exact gm_hcs_of _ _ hφ.2 fun x _ => by simp [gmSingle, hk]

private lemma d_conj_eq_conj_db {n : ℕ} {z : M → V n} (φ : M → ℂ) (j : Fin n) (x : M) :
    d n z j (fun y => conj (φ y)) x = conj (db n z j φ x) := by
  unfold d db
  split_ifs with h
  · set e := Classical.choose h with he_def
    have hc : (fun y => conj (φ y)) ∘ e.symm = Complex.conjCLE ∘ (φ ∘ e.symm) := by
      funext w
      simp
    simp only [wd, wdb]
    rw [hc, Complex.conjCLE.comp_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
      map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
    ring
  · simp

theorem gm_tstar_single (n : ℕ) (z : M → V n) (ph : M → ℝ) (φ : M → ℂ) (j : Fin n) (x : M) :
    tstar n z ph ph (gmSingle ph φ j) x = -((Real.exp (ph x) : ℂ) * conj (db n z j φ x)) := by
  have hfun : ∀ k, (fun y => (Real.exp (-ph y) : ℂ) * gmSingle ph φ j y k) =
      fun y => if k = j then conj (φ y) else 0 := by
    intro k
    funext y
    by_cases hk : k = j
    · subst hk
      have hE : (Real.exp (-ph y) : ℂ) * (Real.exp (ph y) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
      simp only [gmSingle, EuclideanSpace.single_apply, eq_self_iff_true, if_true, ← mul_assoc, hE,
        one_mul]
    · simp [gmSingle, hk]
  have hd : ∀ k, d n z k (fun y => (Real.exp (-ph y) : ℂ) * gmSingle ph φ j y k) x =
      if k = j then conj (db n z j φ x) else 0 := by
    intro k
    rw [hfun k]
    by_cases hk : k = j
    · subst hk
      simp only [eq_self_iff_true, if_true]
      exact d_conj_eq_conj_db φ k x
    · simp only [hk, if_false]
      apply d_eq_zero_of_not_mem_tsupport
      first
        | simp
        | (rw [show (fun _ : M => (0 : ℂ)) = 0 from rfl, tsupport_zero]; simp)
  simp only [tstar, hd, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem gm_ipV_single (n : ℕ) (z : M → V n) (ph : M → ℝ) (F0 φ : M → ℂ) (j : Fin n) :
    ipV n z (dbarF n z F0) (gmSingle ph φ j) ph = conj (∫ x, db n z j F0 x * φ x ∂vol n z) := by
  simp only [ipV, dbarF, gmSingle, EuclideanSpace.inner_single_right]
  rw [← integral_conj]
  congr 1
  funext x
  have hE : (Real.exp (ph x) : ℂ) * (Real.exp (-ph x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  first
    | (simp only [PiLp.toLp_apply, map_mul]
       linear_combination (conj (db n z j F0 x) * conj (φ x)) * hE)
    | (simp only [map_mul]
       linear_combination (conj (db n z j F0 x) * conj (φ x)) * hE)

end maps

section loc

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

theorem locL2_sub_weightedL2 (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : SmoothR n z ph) (F0 : M → ℂ) (hF0 : Continuous F0) (u : Lp ℂ 2 (wvol n z ph)) :
    LocalL2Isometry (vol n z) (fun x => F0 x - u x) := by
  haveI := vol_isFiniteMeasureOnCompacts n z hz
  have hph' := gm_cont_of_smoothR n z hz ph hph
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-ph x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hph'.measurable.neg)
  have hne : ∀ᵐ x ∂vol n z, ENNReal.ofReal (Real.exp (-ph x)) ≠ 0 :=
    Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hac : vol n z ≪ wvol n z ph := by
    rw [wvol]
    first
      | exact withDensity_absolutelyContinuous' hm.aemeasurable hne
      | exact withDensity_absolutelyContinuous' hm hne
  have hu : AEStronglyMeasurable (fun x => u x) (vol n z) := (Lp.aestronglyMeasurable u).mono_ac hac
  have hmeas : AEStronglyMeasurable (fun x => F0 x - u x) (vol n z) :=
    hF0.aestronglyMeasurable.sub hu
  refine ⟨hmeas, fun C hC => ?_⟩
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hF0.continuousOn
  obtain ⟨M0, hM0⟩ := hC.exists_bound_of_continuousOn hph'.continuousOn
  have hCfin : vol n z C < ⊤ := hC.measure_lt_top
  haveI : IsFiniteMeasure ((vol n z).restrict C) := by
    first
      | exact isFiniteMeasure_restrict.2 hCfin.ne
      | exact ⟨by rw [Measure.restrict_apply_univ]; exact hCfin⟩
  have hF0C : MemLp F0 2 ((vol n z).restrict C) :=
    MemLp.of_bound hF0.aestronglyMeasurable.restrict B
      ((ae_restrict_iff' hC.measurableSet).2 (Eventually.of_forall hB))
  have hfin : ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n z ph < ⊤ := by
    rw [← gm_norm_sq u]
    exact ENNReal.ofReal_lt_top
  have hw : ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n z ph =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ) ∂vol n z :=
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
  have hsetle : ∫⁻ x in C, ENNReal.ofReal (Real.exp M0) *
        (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp M0) *
        (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z := by
    first
      | exact setLIntegral_le_lintegral _ _
      | exact lintegral_mono' Measure.restrict_le_self le_rfl
  have huC : MemLp (fun x => u x) 2 ((vol n z).restrict C) := by
    rw [gm_memLp_two_iff _ hu.restrict]
    calc ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂(vol n z).restrict C
        ≤ ∫⁻ x in C, ENNReal.ofReal (Real.exp M0) *
            (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z := by
          refine lintegral_mono_ae ((ae_restrict_iff' hC.measurableSet).2
            (Eventually.of_forall fun x hx => ?_))
          have hle : ph x ≤ M0 :=
            le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hM0 x hx)
          have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp M0) * ENNReal.ofReal (Real.exp (-ph x)) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by linarith))
          calc ‖u x‖ₑ ^ (2:ℝ) = 1 * ‖u x‖ₑ ^ (2:ℝ) := (one_mul _).symm
            _ ≤ (ENNReal.ofReal (Real.exp M0) * ENNReal.ofReal (Real.exp (-ph x))) *
                ‖u x‖ₑ ^ (2:ℝ) := by gcongr
            _ = _ := mul_assoc _ _ _
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp M0) *
            (ENNReal.ofReal (Real.exp (-ph x)) * ‖u x‖ₑ ^ (2:ℝ)) ∂vol n z := hsetle
      _ = ENNReal.ofReal (Real.exp M0) * ∫⁻ x, ‖u x‖ₑ ^ (2:ℝ) ∂wvol n z ph := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hw]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hsub := hF0C.sub huC
  rw [gm_memLp_two_iff _ hsub.1] at hsub
  have e2 : ∀ x, ‖F0 x - u x‖ₑ ^ (2:ℝ) = ‖F0 x - u x‖ₑ ^ 2 := by
    intro x
    first
      | exact ENNReal.rpow_two _
      | exact_mod_cast ENNReal.rpow_natCast _ 2
  simpa [e2] using hsub

end loc

end

end ReciprocityTheory.L2DbarEstimates.F
