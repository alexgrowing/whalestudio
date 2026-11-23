import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem unwBack_small (δ : ℝ≥0∞) (hδ : 0 < δ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ' : ℝ≥0∞, 0 < δ' ∧ ∀ a b : ℝ≥0∞, a < δ' → b < δ' → ENNReal.ofReal C * (a + b) < δ := by
  rcases eq_or_ne δ ⊤ with rfl | hδt
  · refine ⟨1, one_pos, fun a b ha hb => ?_⟩
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨ha.trans ENNReal.one_lt_top, hb.trans ENNReal.one_lt_top⟩)
  have hr0 : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  have hC1 : 0 < C + 1 := by linarith
  have hq : 0 < δ.toReal / (2 * (C + 1)) := div_pos hr0 (by linarith)
  refine ⟨ENNReal.ofReal (δ.toReal / (2 * (C + 1))), ENNReal.ofReal_pos.2 hq, fun a b ha hb => ?_⟩
  have hat : a ≠ ⊤ := (ha.trans ENNReal.ofReal_lt_top).ne
  have hbt : b ≠ ⊤ := (hb.trans ENNReal.ofReal_lt_top).ne
  have ha' : a.toReal < δ.toReal / (2 * (C + 1)) := by
    have h1 := (ENNReal.toReal_lt_toReal hat ENNReal.ofReal_ne_top).2 ha
    rwa [ENNReal.toReal_ofReal hq.le] at h1
  have hb' : b.toReal < δ.toReal / (2 * (C + 1)) := by
    have h1 := (ENNReal.toReal_lt_toReal hbt ENNReal.ofReal_ne_top).2 hb
    rwa [ENNReal.toReal_ofReal hq.le] at h1
  have hs : 0 ≤ a.toReal + b.toReal := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hlt : C * (a.toReal + b.toReal) < δ.toReal := by
    have h1 : C * (a.toReal + b.toReal) ≤ (C + 1) * (a.toReal + b.toReal) :=
      mul_le_mul_of_nonneg_right (by linarith) hs
    have h2 : (C + 1) * (a.toReal + b.toReal) < (C + 1) * (2 * (δ.toReal / (2 * (C + 1)))) :=
      mul_lt_mul_of_pos_left (by linarith) hC1
    have h3 : (C + 1) * (2 * (δ.toReal / (2 * (C + 1)))) = δ.toReal := by
      field_simp
    linarith
  calc ENNReal.ofReal C * (a + b) = ENNReal.ofReal (C * (a.toReal + b.toReal)) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hat, ENNReal.ofReal_toReal hbt]
    _ < ENNReal.ofReal δ.toReal := (ENNReal.ofReal_lt_ofReal_iff hr0).2 hlt
    _ = δ := ENNReal.ofReal_toReal hδt

theorem unwBack_bound {M : Type*} [TopologicalSpace M] (K : Set M) (hK : IsCompact K) (F : M → ℝ)
    (hF : Continuous F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, F x ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have h1 := hC x hx
  rw [Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans (h1.trans (le_max_left _ _))

theorem unwBack_lint {M : Type*} [MeasurableSpace M] (μ : Measure M) (F G : M → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, F x ≤ C * G x) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (G x) ∂μ :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_mul hC]
          exact ENNReal.ofReal_le_ofReal (h x)
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (G x) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem unwBack_lint2 {M : Type*} [MeasurableSpace M] (μ : Measure M) (F A B : M → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hBm : AEMeasurable (fun x => ENNReal.ofReal (B x)) μ) (h : ∀ x, F x ≤ C * (A x + B x)) :
    ∫⁻ x, ENNReal.ofReal (F x) ∂μ ≤ ENNReal.ofReal C *
      (∫⁻ x, ENNReal.ofReal (A x) ∂μ + ∫⁻ x, ENNReal.ofReal (B x) ∂μ) := by
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂μ
      ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (A x + B x) ∂μ :=
        unwBack_lint μ F (fun x => A x + B x) C hC h
    _ = ENNReal.ofReal C * (∫⁻ x, ENNReal.ofReal (A x) ∂μ + ∫⁻ x, ENNReal.ofReal (B x) ∂μ) := by
        rw [← lintegral_add_right' (fun x => ENNReal.ofReal (A x)) hBm]
        congr 1
        exact lintegral_congr fun x => ENNReal.ofReal_add (hA x) (hB x)

theorem unwBack_exp_sq (a : ℝ) : Real.exp a ^ 2 * Real.exp (-a) = Real.exp a := by
  rw [sq, mul_assoc, ← Real.exp_add]
  simp

theorem unwBack_norm_exp (a : ℝ) : ‖(Real.exp a : ℂ)‖ = Real.exp a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos a)]

theorem unwBack_norm_add_sq {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h2 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    gcongr
    exact norm_add_le u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem sqNorm_wedge_twist_le {n : ℕ} (a : ℂ) (A : Fin n → Fin n → ℂ) (c : Fin n → ℂ) (B : V n) :
    sq2 n (fun j k => a * A j k + a * wedge c (fun i => B i) j k) ≤
      ‖a‖ ^ 2 * (2 + 4 * ∑ j, ‖c j‖ ^ 2) * (sq2 n A + ‖B‖ ^ 2) := by
  simp only [sq2, wedge]
  have hB : ‖B‖ ^ 2 = ∑ i, ‖B i‖ ^ 2 := EuclideanSpace.norm_sq_eq B
  have h1 : ∀ j k, ‖c j * B k - c k * B j‖ ^ 2 ≤
      2 * (‖c j‖ ^ 2 * ‖B k‖ ^ 2) + 2 * (‖c k‖ ^ 2 * ‖B j‖ ^ 2) := by
    intro j k
    have h := unwBack_norm_add_sq (c j * B k) (-(c k * B j))
    rw [← sub_eq_add_neg, norm_neg, norm_mul, norm_mul, mul_pow, mul_pow] at h
    linarith
  have e2 : ∑ j, ∑ k, ‖c k‖ ^ 2 * ‖B j‖ ^ 2 = ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2 :=
    Finset.sum_comm
  have e3 : ∑ j, ∑ k, ‖c j‖ ^ 2 * ‖B k‖ ^ 2 = (∑ j, ‖c j‖ ^ 2) * ∑ k, ‖B k‖ ^ 2 := by
    rw [Finset.sum_mul_sum]
  have hW : ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2 ≤ 4 * (∑ j, ‖c j‖ ^ 2) * ‖B‖ ^ 2 := by
    calc ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2
        ≤ ∑ j, ∑ k, (2 * (‖c j‖ ^ 2 * ‖B k‖ ^ 2) + 2 * (‖c k‖ ^ 2 * ‖B j‖ ^ 2)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h1 j k
      _ = 4 * (∑ j, ‖c j‖ ^ 2) * ‖B‖ ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [e2, e3, hB]
          simp only [← Finset.sum_mul]
          ring
  have hA : ∀ j k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤
      ‖a‖ ^ 2 * (2 * ‖A j k‖ ^ 2 + 2 * ‖c j * B k - c k * B j‖ ^ 2) := by
    intro j k
    rw [← mul_add, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left (unwBack_norm_add_sq _ _) (by positivity)
  have hsum : ∑ j, ∑ k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2 ≤
      ‖a‖ ^ 2 * (2 * ∑ j, ∑ k, ‖A j k‖ ^ 2 + 2 * ∑ j, ∑ k, ‖c j * B k - c k * B j‖ ^ 2) := by
    calc ∑ j, ∑ k, ‖a * A j k + a * (c j * B k - c k * B j)‖ ^ 2
        ≤ ∑ j, ∑ k, ‖a‖ ^ 2 * (2 * ‖A j k‖ ^ 2 + 2 * ‖c j * B k - c k * B j‖ ^ 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hA j k
      _ = _ := by simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  have hα : 0 ≤ ‖a‖ ^ 2 := by positivity
  have hS : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hSA : 0 ≤ ∑ j, ∑ k, ‖A j k‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity
  have hb : 0 ≤ ‖B‖ ^ 2 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hW hα
  have k2 := mul_nonneg hα hb
  have k3 := mul_nonneg (mul_nonneg hα hS) hSA
  nlinarith [hsum, k1, k2, k3]

theorem unwBack_contR {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by
  unfold SmoothR Smooth at hph
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, hze⟩ := hz x
  have hch : IsChart n z e := fun y _ => by rw [hze]
  have hc : ContinuousAt ((fun y => (ph y : ℂ)) ∘ e.symm) (e x) :=
    ((hph e hch).continuousOn).continuousAt (e.open_target.mem_nhds (e.map_source hx))
  have hc2 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x :=
    hc.comp (e.continuousAt hx)
  have hc3 : ContinuousAt (fun y => (ph y : ℂ)) x := by
    refine hc2.congr ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  exact (Complex.continuous_re.continuousAt.comp hc3).congr
    (Filter.Eventually.of_forall fun y => by simp)

theorem unwBack_off {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (K0 : Set M) (hK0 : IsCompact K0) (u : M → ℂ) (hu : ∀ x, x ∉ K0 → u x = 0) (x : M)
    (hx : x ∉ K0) (j : Fin n) : d n z j u x = 0 ∧ db n z j u x = 0 := by
  have key : ∀ h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source,
      fderiv ℝ (u ∘ (Classical.choose h).symm) (z x) = 0 := by
    intro h
    obtain ⟨he, hx'⟩ := Classical.choose_spec h
    set e := Classical.choose h
    have hzx : z x = e x := he hx'
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ) := by
      rw [hzx]
      have hopen : IsOpen K0ᶜ := hK0.isClosed.isOpen_compl
      have hc : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hx')
      have hmem : K0ᶜ ∈ 𝓝 (e.symm (e x)) := by
        rw [e.left_inv hx']
        exact hopen.mem_nhds hx
      filter_upwards [hc.preimage_mem_nhds hmem] with y hy
      exact hu _ hy
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  unfold d db wd wdb
  constructor
  · split_ifs with h
    · rw [key h]
      simp
    · rfl
  · split_ifs with h
    · rw [key h]
      simp
    · rfl

theorem smooth_ofReal_secondWeight {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ψ : M → ℝ)
    (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    Smooth n z (fun y => ((w2 ph ψ y : ℝ) : ℂ)) := by
  unfold SmoothR at hph hψ
  unfold Smooth at hph hψ ⊢
  intro e he
  refine ((hph e he).sub (hψ e he)).congr fun p _ => ?_
  simp [w2]

theorem unwBack_smooth_exp {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (u : M → ℝ)
    (hu : Smooth n z (fun y => (u y : ℂ))) : Smooth n z (fun y => (Real.exp (u y) : ℂ)) := by
  unfold Smooth at hu ⊢
  intro e he
  have hg : ContDiff ℝ ∞ (fun w : ℂ => ((Real.exp w.re : ℝ) : ℂ)) := by
    first
    | fun_prop
    | exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.reCLM.contDiff)
  refine (hg.comp_contDiffOn (hu e he)).congr fun p _ => ?_
  simp [Function.comp]

end

end ReciprocityTheory.L2DbarEstimates.F
