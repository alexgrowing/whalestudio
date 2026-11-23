import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierTransformMatrixSpaceInvolution

noncomputable section

open MeasureTheory Ad3.K Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealWeil

def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem ee_zero : ee 0 = 1 := by simp [ee]

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  have : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

def Fr (Φ : ℂ → ℂ) (z : ℂ) : ℂ := ∫ u, ee (2 * (conj z * u).re) * Φ u ∂volC

theorem rWR_zero (a b d : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b 0 d Φ z = ee (a * b * Complex.normSq z) * sgR a * ((|a| : ℝ) : ℂ) * Φ ((a : ℂ) * z) := by
  simp only [rWR, if_true, ee]

theorem rWR_ne (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * sgR (-c) * ((|c|⁻¹ : ℝ) : ℂ) *
      ∫ u, ee ((a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c) * Φ u ∂volC := by
  simp only [rWR, if_neg hc, ee]

theorem rWR_fr (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * sgR (-c) * ((|c|⁻¹ : ℝ) : ℂ) * (ee (a / c * Complex.normSq z) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z)) := by
  rw [rWR_ne a b d hc, Fr, ← integral_const_mul (μ := volC) (ee (a / c * Complex.normSq z))]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have e : (a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c =
      a / c * Complex.normSq z + (2 * (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re + d / c * Complex.normSq u) := by
    have : (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re = -c⁻¹ * (conj z * u).re := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    rw [this]
    field_simp
    ring
  show ee _ * Φ u = ee _ * (ee _ * (ee _ * Φ u))
  rw [e, ee_add, ee_add]
  ring

theorem integral_volC (f : ℂ → ℂ) : ∫ u, f u ∂volC = 2 * ∫ u, f u := by
  rw [volC, integral_smul_measure]
  simp

theorem integral_volC_smul (f : ℂ → ℂ) {s : ℝ} (hs : s ≠ 0) :
    ∫ u, f ((s : ℂ) * u) ∂volC = (((s ^ 2)⁻¹ : ℝ) : ℂ) * ∫ u, f u ∂volC := by
  have h := Measure.integral_comp_smul (volume : Measure ℂ) f s
  simp only [Complex.real_smul, Complex.finrank_real_complex] at h
  rw [integral_volC, integral_volC, h, abs_of_pos (by positivity : 0 < (s ^ 2)⁻¹)]
  ring_nf

theorem sgR_mul_abs {a : ℝ} (ha : a ≠ 0) : sgR a * ((|a| : ℝ) : ℂ) = (a : ℂ) := by
  rcases lt_or_gt_of_ne ha with h1 | h1
  · simp [sgR, h1.le.not_gt, abs_of_neg h1]
  · simp [sgR, h1, abs_of_pos h1]

theorem sgR_mul_abs_inv {a : ℝ} (ha : a ≠ 0) : sgR a * ((|a|⁻¹ : ℝ) : ℂ) = ((a⁻¹ : ℝ) : ℂ) := by
  rcases lt_or_gt_of_ne ha with h1 | h1
  · simp [sgR, h1.le.not_gt, abs_of_neg h1]
  · simp [sgR, h1, abs_of_pos h1]

def Gs (ε t : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi / ((ε : ℂ) - 2 * Real.pi * t * Complex.I)) *
    Complex.exp (-(4 * Real.pi ^ 2 * (Complex.normSq w : ℂ)) / ((ε : ℂ) - 2 * Real.pi * t * Complex.I))

open Filter Topology
open scoped FourierTransform

theorem const_mem (k : ℂ) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : (fun z => k * Φ z) ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  exact ⟨k • f, by funext z; simp⟩

theorem dil_mem {s : ℝ} (hs : s ≠ 0) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : (fun z => Φ ((s : ℂ) * z)) ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  let L : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 s hs)
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, ?_⟩
  funext z
  simp [L, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

theorem chirp_mem (t : ℝ) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : (fun z => ee (t * Complex.normSq z) * Φ z) ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  refine ⟨GlobalTheory.CompanionTheory.Kloc.Fresnel.chirpS t f, ?_⟩
  funext z
  rw [GlobalTheory.CompanionTheory.Kloc.Fresnel.chirpS_apply]
  congr 1
  simp only [GlobalTheory.CompanionTheory.Kloc.Fresnel.chirp, ee]
  rw [Complex.normSq_eq_norm_sq]
  congr 1
  push_cast
  ring

theorem inner_eq (v z : ℂ) : inner ℝ v z = (conj z * v).re := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem Fr_eq (Φ : ℂ → ℂ) (z : ℂ) : Fr Φ z = 2 * 𝓕 Φ (((-2 : ℝ) : ℂ) * z) := by
  rw [Fr, integral_volC, Real.fourier_eq']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [ee, smul_eq_mul]
  congr 2
  have h : inner ℝ v (((-2 : ℝ) : ℂ) * z) = -2 * (conj z * v).re := by
    rw [inner_eq, map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
  rw [h]
  push_cast
  ring

theorem Fr_mem {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : Fr Φ ∈ SchC := by
  obtain ⟨f, rfl⟩ := hΦ
  have e : Fr ⇑f = fun z => 2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * z) := funext (Fr_eq _)
  rw [e]
  exact const_mem 2 (dil_mem (by norm_num) ⟨(𝓕 f : SchwartzMap ℂ ℂ), SchwartzMap.fourier_coe f⟩)

theorem Fr_Fr {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) (z : ℂ) : Fr (Fr Φ) z = Φ (-z) := by
  obtain ⟨f, rfl⟩ := hΦ
  have e : Fr ⇑f = fun z => 2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * z) := funext (Fr_eq _)
  have hint : Integrable (𝓕 (f : ℂ → ℂ)) := by
    have := (𝓕 f).integrable (μ := volume)
    rwa [SchwartzMap.fourier_coe] at this
  have hinv := congrFun (Continuous.fourierInv_fourier_eq f.continuous (f.integrable (μ := volume)) hint) (-z)
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv, e, Fr]
  set k : ℂ → ℂ := fun v => ee (-(conj z * v).re) * (2 * 𝓕 (⇑f) v) with hk
  have h := integral_volC_smul k (by norm_num : (-2 : ℝ) ≠ 0)
  have h1 : ∫ u, ee (2 * (conj z * u).re) * (2 * 𝓕 (⇑f) (((-2 : ℝ) : ℂ) * u)) ∂volC = ∫ u, k (((-2 : ℝ) : ℂ) * u) ∂volC := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hk]
    congr 2
    rw [mul_left_comm, Complex.re_ofReal_mul]
    ring
  rw [h1, h, integral_volC, ← mul_assoc]
  have h2 : (((((-2 : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * 2) = 2⁻¹ := by
    push_cast
    norm_num
  rw [h2, hk]
  simp only []
  have h3 : ∀ v : ℂ, ee (-(conj z * v).re) * (2 * 𝓕 (⇑f) v) = 2 * (Complex.exp (((2 * Real.pi * inner ℝ v (-z) : ℝ) : ℂ) * Complex.I) • 𝓕 (⇑f) v) := by
    intro v
    have : inner ℝ v (-z) = -(conj z * v).re := by
      rw [inner_neg_right, inner_eq]
    rw [this, ee, smul_eq_mul]
    have e4 : 2 * (Real.pi : ℂ) * Complex.I * ((-(conj z * v).re : ℝ) : ℂ) = ((2 * Real.pi * -(conj z * v).re : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e4]
    ring
  simp only [h3]
  rw [integral_const_mul]
  simp

theorem gauss_int (ε t : ℝ) (hε : 0 < ε) (w : ℂ) :
    ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC = Gs ε t w := by
  set b : ℂ := (ε : ℂ) - 2 * Real.pi * t * Complex.I with hbd
  have hb : 0 < b.re := by simpa [hbd] using hε
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    simp at hb
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb (((-2 : ℝ) : ℂ) * w)
  have e1 : ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC =
      Fr (fun v : ℂ => Complex.exp (-b * (‖v‖ : ℂ) ^ 2)) w := by
    rw [Fr]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show Complex.exp _ * ee _ = ee _ * Complex.exp _
    rw [ee_add]
    simp only [ee]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Complex.normSq_eq_norm_sq, hbd]
    congr 1
    push_cast
    ring
  rw [e1, Fr_eq, h, Gs, ← hbd]
  simp only [Complex.finrank_real_complex]
  have e2 : (((2 : ℕ) : ℂ) / 2) = 1 := by norm_num
  rw [e2, Complex.cpow_one, norm_mul, Complex.normSq_eq_norm_sq]
  have e3 : ‖((-2 : ℝ) : ℂ)‖ = 2 := by simp
  rw [e3]
  rw [← mul_assoc]
  congr 1
  · ring
  · congr 1
    push_cast
    ring

theorem fubini_Fr {K Ψ : ℂ → ℂ} (hK : Integrable K volC) (hKc : Continuous K) (hΨ : Ψ ∈ SchC) (z : ℂ) :
    ∫ y, K y * ee (2 * (conj z * y).re) * Fr Ψ y ∂volC =
      ∫ u, (∫ y, K y * ee (2 * (conj (z + u) * y).re) ∂volC) * Ψ u ∂volC := by
  have hΨi : Integrable Ψ volC := by
    obtain ⟨f, rfl⟩ := hΨ
    have h : Integrable (⇑f) (volume : Measure ℂ) := f.integrable
    exact h.smul_measure (by simp)
  have hΨc : Continuous Ψ := by
    obtain ⟨f, rfl⟩ := hΨ
    exact f.continuous
  haveI : SFinite volC := by
    unfold volC
    infer_instance
  have hF : Integrable (Function.uncurry fun (y u : ℂ) => K y * ee (2 * (conj (z + u) * y).re) * Ψ u) (volC.prod volC) := by
    have base := Integrable.mul_prod hK hΨi
    refine base.mono ?_ (Eventually.of_forall fun p => ?_)
    · apply Continuous.aestronglyMeasurable
      have := continuous_ee
      simp only [Function.uncurry_def]
      fun_prop
    · simp only [Function.uncurry_def, norm_mul, norm_ee, mul_one, le_refl]
  have hsw := integral_integral_swap hF
  calc _ = ∫ y, ∫ u, K y * ee (2 * (conj (z + u) * y).re) * Ψ u ∂volC ∂volC := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show _ * _ * (∫ u, _ ∂volC) = _
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show _ = K y * ee _ * Ψ u
        have e : 2 * (conj (z + u) * y).re = 2 * (conj z * y).re + 2 * (conj y * u).re := by
          simp only [map_add, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
          ring
        rw [e, ee_add]
        ring
    _ = ∫ u, ∫ y, K y * ee (2 * (conj (z + u) * y).re) * Ψ u ∂volC ∂volC := hsw
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        exact integral_mul_const _ _

theorem norm_exp_reg_le {ε : ℝ} (hε : 0 < ε) (y : ℂ) : ‖Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  refine Real.exp_le_one_iff.2 ?_
  have := Complex.normSq_nonneg y
  simp only [Complex.neg_re, Complex.ofReal_re]
  have : 0 ≤ ε * Complex.normSq y := by positivity
  linarith

theorem tendsto_reg_left {f : ℂ → ℂ} (hf : Integrable f volC) :
    Tendsto (fun ε : ℝ => ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * f y ∂volC) (𝓝[>] 0) (𝓝 (∫ y, f y ∂volC)) := by
  have hs := Complex.continuous_normSq
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖) ?_ ?_ hf.norm ?_
  · refine Eventually.of_forall fun ε => ?_
    refine Continuous.aestronglyMeasurable ?_ |>.mul hf.aestronglyMeasurable
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_exp_reg_le hε y)
  · refine Eventually.of_forall fun y => ?_
    have hc : Continuous fun ε : ℝ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * f y := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this

theorem norm_Gs_le {ε t : ℝ} (hε : 0 < ε) (ht : t ≠ 0) (w : ℂ) : ‖Gs ε t w‖ ≤ |t|⁻¹ := by
  set b : ℂ := (ε : ℂ) - 2 * Real.pi * t * Complex.I with hbd
  have hre : b.re = ε := by simp [hbd]
  have him : b.im = -(2 * Real.pi * t) := by simp [hbd]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hpi := Real.pi_pos
  have ht' : 0 < |t| := abs_pos.2 ht
  have hnb : 2 * Real.pi * |t| ≤ ‖b‖ := by
    have h1 := Complex.abs_im_le_norm b
    rw [him, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h1
    exact h1
  have h1 : ‖2 * (Real.pi : ℂ) / b‖ ≤ |t|⁻¹ := by
    rw [norm_div]
    have : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos hpi]
    rw [this, div_le_iff₀ (norm_pos_iff.2 hb0)]
    have : |t|⁻¹ * (2 * Real.pi * |t|) ≤ |t|⁻¹ * ‖b‖ := mul_le_mul_of_nonneg_left hnb (by positivity)
    have e : |t|⁻¹ * (2 * Real.pi * |t|) = 2 * Real.pi := by
      field_simp
    linarith
  have h2 : ‖Complex.exp (-(4 * Real.pi ^ 2 * (Complex.normSq w : ℂ)) / b)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.2 ?_
    have e : -(4 * (Real.pi : ℂ) ^ 2 * (Complex.normSq w : ℂ)) / b = ((-(4 * Real.pi ^ 2 * Complex.normSq w) : ℝ) : ℂ) / b := by
      push_cast
      ring
    rw [e, Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero, hre]
    have hN := Complex.normSq_nonneg w
    have : 0 ≤ (4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b :=
      div_nonneg (by positivity) (Complex.normSq_nonneg _)
    have e2 : -(4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b = -((4 * Real.pi ^ 2 * Complex.normSq w) * ε / Complex.normSq b) := by ring
    rw [e2]
    linarith
  rw [Gs, ← hbd, norm_mul]
  calc _ ≤ |t|⁻¹ * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem tendsto_Gs {t : ℝ} (ht : t ≠ 0) (w : ℂ) :
    Tendsto (fun ε : ℝ => Gs ε t w) (𝓝[>] 0) (𝓝 ((Complex.I / (t : ℂ)) * ee (-(Complex.normSq w) / t))) := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb0 : ((0 : ℝ) : ℂ) - 2 * Real.pi * t * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, ht]
  have hbc : Continuous fun ε : ℝ => (ε : ℂ) - 2 * Real.pi * t * Complex.I := by fun_prop
  have hb := hbc.tendsto 0
  have h1 : Tendsto (fun ε : ℝ => Gs ε t w) (𝓝 0) (𝓝 (Gs 0 t w)) := by
    unfold Gs
    exact (tendsto_const_nhds.div hb hb0).mul ((tendsto_const_nhds.div hb hb0).cexp)
  have hv : Gs 0 t w = (Complex.I / (t : ℂ)) * ee (-(Complex.normSq w) / t) := by
    unfold Gs ee
    congr 1
    · rw [Complex.ofReal_zero, zero_sub, div_eq_div_iff (by simp [Real.pi_ne_zero, ht]) htc]
      ring_nf
      simp only [Complex.I_sq]
      ring
    · congr 1
      rw [Complex.ofReal_zero, zero_sub, div_eq_iff (by simp [Real.pi_ne_zero, ht])]
      push_cast
      field_simp
      ring_nf
      simp only [Complex.I_sq]
      ring
  rw [← hv]
  exact h1.mono_left nhdsWithin_le_nhds

theorem tendsto_reg_right {t : ℝ} (ht : t ≠ 0) {Ψ : ℂ → ℂ} (hΨ : Integrable Ψ volC) (z : ℂ) :
    Tendsto (fun ε : ℝ => ∫ u, Gs ε t (z + u) * Ψ u ∂volC) (𝓝[>] 0)
      (𝓝 ((Complex.I / (t : ℂ)) * ∫ u, ee (-(Complex.normSq (z + u)) / t) * Ψ u ∂volC)) := by
  rw [← integral_const_mul]
  have hcont : ∀ ε : ℝ, 0 < ε → Continuous fun u => Gs ε t (z + u) := by
    intro ε hε
    have hs := Complex.continuous_normSq
    unfold Gs
    fun_prop
  refine tendsto_integral_filter_of_dominated_convergence (fun u => |t|⁻¹ * ‖Ψ u‖) ?_ ?_ (hΨ.norm.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hcont ε hε).aestronglyMeasurable.mul hΨ.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun u => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_Gs_le hε ht _) (norm_nonneg _)
  · refine Eventually.of_forall fun u => ?_
    have := (tendsto_Gs ht (z + u)).mul_const (Ψ u)
    simpa [mul_assoc] using this

theorem sch_integrable {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : Integrable Φ volC := by
  obtain ⟨f, rfl⟩ := hΦ
  have h : Integrable (⇑f) (volume : Measure ℂ) := f.integrable
  exact h.smul_measure (by simp)

theorem gauss {t : ℝ} (ht : t ≠ 0) {Ψ : ℂ → ℂ} (hΨ : Ψ ∈ SchC) (z : ℂ) :
    ∫ y, ee (t * Complex.normSq y + 2 * (conj z * y).re) * Fr Ψ y ∂volC =
      (Complex.I / (t : ℂ)) * ∫ u, ee (-(Complex.normSq (z + u)) / t) * Ψ u ∂volC := by
  have hFi := sch_integrable (Fr_mem hΨ)
  have hf : Integrable (fun y => ee (t * Complex.normSq y + 2 * (conj z * y).re) * Fr Ψ y) volC := by
    refine hFi.bdd_mul (c := 1) ?_ ?_
    · exact (continuous_ee.comp (by fun_prop)).aestronglyMeasurable
    · exact Eventually.of_forall fun y => (norm_ee _).le
  have hL := tendsto_reg_left hf
  have hR := tendsto_reg_right ht (sch_integrable hΨ) z
  refine tendsto_nhds_unique (hL.congr' ?_) hR
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := hε
  have hKc : Continuous fun y : ℂ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y) := by
    have := continuous_ee
    have := Complex.continuous_normSq
    fun_prop
  have hKi : Integrable (fun y : ℂ => Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y)) volC := by
    have hb : 0 < ((ε : ℂ) - 2 * Real.pi * t * Complex.I).re := by simpa using hε'
    have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0
    have h1 : Integrable (fun y : ℂ => Complex.exp (-((ε : ℂ) - 2 * Real.pi * t * Complex.I) * (‖y‖ : ℂ) ^ 2)) (volume : Measure ℂ) := by
      simpa using h0
    have h2 := h1.smul_measure (c := (2 : ENNReal)) (by simp)
    refine h2.congr (Eventually.of_forall fun y => ?_)
    simp only [ee, ← Complex.exp_add]
    congr 1
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have h := fubini_Fr hKi hKc hΨ z
  calc _ = ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) * ee (t * Complex.normSq y) * ee (2 * (conj z * y).re) * Fr Ψ y ∂volC := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [ee_add]
        ring
    _ = _ := h
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only []
        rw [← gauss_int ε t hε']
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [ee_add]
        ring

theorem rWR_zero' {a : ℝ} (ha : a ≠ 0) (b d : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b 0 d Φ z = ee (a * b * Complex.normSq z) * (a : ℂ) * Φ ((a : ℂ) * z) := by
  rw [rWR_zero, mul_assoc (ee _), sgR_mul_abs ha]

theorem rWR_ne' (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * ((-c⁻¹ : ℝ) : ℂ) *
      ∫ u, ee ((a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c) * Φ u ∂volC := by
  have h := sgR_mul_abs_inv (neg_ne_zero.2 hc)
  rw [abs_neg, inv_neg] at h
  rw [rWR_ne a b d hc, mul_assoc Complex.I, h]

theorem rWR_fr' (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR a b c d Φ z = Complex.I * ((-c⁻¹ : ℝ) : ℂ) * (ee (a / c * Complex.normSq z) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z)) := by
  have h := sgR_mul_abs_inv (neg_ne_zero.2 hc)
  rw [abs_neg, inv_neg] at h
  rw [rWR_fr a b d hc, mul_assoc Complex.I, h]

theorem rWR_n (x : ℝ) (F : ℂ → ℂ) (z : ℂ) : rWR 1 x 0 1 F z = ee (x * Complex.normSq z) * F z := by
  rw [rWR_zero' one_ne_zero]
  simp

theorem rWR_m {s : ℝ} (hs : s ≠ 0) (F : ℂ → ℂ) (z : ℂ) : rWR s 0 0 s⁻¹ F z = (s : ℂ) * F ((s : ℂ) * z) := by
  rw [rWR_zero' hs]
  simp

theorem Pn (x a b c d : ℝ) (h : a * d - b * c = 1) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR (a + x * c) (b + x * d) c d Φ z = rWR 1 x 0 1 (rWR a b c d Φ) z := by
  rw [rWR_n]
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    rw [rWR_zero, rWR_zero]
    have e : (a + x * 0) * (b + x * d) * Complex.normSq z = x * Complex.normSq z + a * b * Complex.normSq z := by
      linear_combination (x * Complex.normSq z) * had
    rw [e, ee_add]
    simp only [mul_zero, add_zero]
    ring
  · rw [rWR_ne' _ _ _ hc, rWR_ne' _ _ _ hc, mul_left_comm, ← integral_const_mul (μ := volC) (ee (x * Complex.normSq z))]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ee _ * Φ u = ee _ * (ee _ * Φ u)
    rw [← mul_assoc, ← ee_add]
    congr 2
    field_simp
    ring

theorem Pm {s : ℝ} (hs : s ≠ 0) (a b c d : ℝ) (h : a * d - b * c = 1) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR (s * a) (s * b) (c / s) (d / s) Φ z = rWR s 0 0 s⁻¹ (rWR a b c d Φ) z := by
  rw [rWR_m hs]
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    rw [zero_div, rWR_zero' (mul_ne_zero hs ha), rWR_zero' ha, Complex.normSq_mul, Complex.normSq_ofReal]
    have e : s * a * (s * b) * Complex.normSq z = a * b * (s * s * Complex.normSq z) := by ring
    rw [e]
    push_cast
    ring_nf
  · have hcs : c / s ≠ 0 := div_ne_zero hc hs
    rw [rWR_ne' _ _ _ hcs, rWR_ne' _ _ _ hc]
    have hI : ∫ u, ee ((s * a * Complex.normSq z + d / s * Complex.normSq u - 2 * (conj z * u).re) / (c / s)) * Φ u ∂volC =
        ∫ u, ee ((a * Complex.normSq ((s : ℂ) * z) + d * Complex.normSq u - 2 * (conj ((s : ℂ) * z) * u).re) / c) * Φ u ∂volC := by
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show ee _ * Φ u = ee _ * Φ u
      have e2 : (conj ((s : ℂ) * z) * u).re = s * (conj z * u).re := by
        rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
      rw [e2, Complex.normSq_mul, Complex.normSq_ofReal]
      congr 2
      field_simp
    rw [hI]
    push_cast
    field_simp

theorem Pw_common (a b d : ℝ) {c : ℝ} (hc : c ≠ 0) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR 0 1 (-1) 0 (rWR a b c d Φ) z = (c : ℂ) * ∫ v, ee (a * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v ∂volC := by
  rw [rWR_ne' 0 1 0 (by norm_num : (-1 : ℝ) ≠ 0)]
  set H : ℂ → ℂ := fun u => ee ((0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1)) * rWR a b c d Φ u with hH
  have hs : (-c : ℝ) ≠ 0 := neg_ne_zero.2 hc
  have h := integral_volC_smul H hs
  have h2 : ∫ u, H u ∂volC = ((c ^ 2 : ℝ) : ℂ) * ∫ u, H (((-c : ℝ) : ℂ) * u) ∂volC := by
    rw [h, neg_sq, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 hc)]
    simp
  show Complex.I * (((-(-1 : ℝ)⁻¹ : ℝ)) : ℂ) * ∫ u, H u ∂volC = _
  rw [h2]
  have h3 : ∀ v : ℂ, H (((-c : ℝ) : ℂ) * v) = (Complex.I * ((-c⁻¹ : ℝ) : ℂ)) * (ee (a * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v) := by
    intro v
    simp only [hH]
    rw [rWR_fr' a b d hc]
    have e1 : (((-c⁻¹ : ℝ) : ℂ) * (((-c : ℝ) : ℂ) * v)) = v := by
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      push_cast
      field_simp
    have e2 : (conj (((-c : ℝ) : ℂ) * z) * v).re = -c * (conj z * v).re := by
      rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
    have e3 : (conj z * (((-c : ℝ) : ℂ) * v)).re = -c * (conj z * v).re := by
      rw [mul_left_comm, Complex.re_ofReal_mul]
    rw [e1, ee_add, e2, e3, Complex.normSq_mul, Complex.normSq_ofReal]
    have e4 : (0 * Complex.normSq z + 0 * (Complex.normSq ((-c : ℝ) : ℂ) * Complex.normSq v) - 2 * (-c * (conj z * v).re)) / (-1) = 2 * (-c * (conj z * v).re) := by ring
    have e5 : (0 * Complex.normSq z + 0 * (-c * -c * Complex.normSq v) - 2 * (-c * (conj z * v).re)) / (-1) = 2 * (-c * (conj z * v).re) := by ring
    have e6 : a / c * (-c * -c * Complex.normSq v) = a * c * Complex.normSq v := by
      field_simp
    rw [e5, e6]
    ring
  simp only [h3]
  rw [integral_const_mul]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

theorem Pw0 {a b d : ℝ} (had : a * d = 1) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR 0 d (-a) (-b) Φ z = rWR 0 1 (-1) 0 (rWR a b 0 d Φ) z := by
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
  have ha' : -a ≠ 0 := neg_ne_zero.2 ha
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  rw [rWR_ne' _ _ _ ha', rWR_ne' 0 1 0 (by norm_num : (-1 : ℝ) ≠ 0)]
  set f : ℂ → ℂ := fun u => ee ((0 * Complex.normSq z + -b * Complex.normSq u - 2 * (conj z * u).re) / (-a)) * Φ u with hf
  have h := integral_volC_smul f ha
  have h1 : ∫ u, ee ((0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1)) * rWR a b 0 d Φ u ∂volC =
      (a : ℂ) * ∫ u, f ((a : ℂ) * u) ∂volC := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show _ * _ = (a : ℂ) * (ee _ * Φ _)
    rw [rWR_zero' ha]
    have e2 : (conj z * ((a : ℂ) * u)).re = a * (conj z * u).re := by
      rw [mul_left_comm, Complex.re_ofReal_mul]
    have e : (0 * Complex.normSq z + -b * Complex.normSq ((a : ℂ) * u) - 2 * (conj z * ((a : ℂ) * u)).re) / (-a) =
        (0 * Complex.normSq z + 0 * Complex.normSq u - 2 * (conj z * u).re) / (-1) + a * b * Complex.normSq u := by
      rw [e2, Complex.normSq_mul, Complex.normSq_ofReal]
      field_simp
      ring
    rw [e, ee_add]
    ring
  show Complex.I * _ * ∫ u, f u ∂volC = _
  rw [h1, h]
  push_cast
  field_simp

theorem Pw1 {b c d : ℝ} (hbc : b * c = -1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) (z : ℂ) :
    rWR c d 0 (-b) Φ z = rWR 0 1 (-1) 0 (rWR 0 b c d Φ) z := by
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hbc
  have hΨ := chirp_mem (d / c) hΦ
  rw [Pw_common 0 b d hc, rWR_zero' hc]
  have h1 : ∫ v, ee (0 * c * Complex.normSq v + 2 * (conj (((-c : ℝ) : ℂ) * z) * v).re) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) v ∂volC = Fr (Fr (fun u => ee (d / c * Complex.normSq u) * Φ u)) (((-c : ℝ) : ℂ) * z) := by
    rw [Fr]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp
  rw [h1, Fr_Fr hΨ]
  have e : -(((-c : ℝ) : ℂ) * z) = (c : ℂ) * z := by
    push_cast
    ring
  rw [e, Complex.normSq_mul, Complex.normSq_ofReal]
  have e2 : d / c * (c * c * Complex.normSq z) = c * d * Complex.normSq z := by
    field_simp
  rw [e2]
  ring

theorem Pw2 {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (h : a * d - b * c = 1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) (z : ℂ) :
    rWR c d (-a) (-b) Φ z = rWR 0 1 (-1) 0 (rWR a b c d Φ) z := by
  have hΨ := chirp_mem (d / c) hΦ
  have ha' : -a ≠ 0 := neg_ne_zero.2 ha
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [Pw_common a b d hc, gauss (mul_ne_zero ha hc) hΨ, rWR_ne' _ _ _ ha']
  have h1 : ∫ u, ee (-(Complex.normSq (((-c : ℝ) : ℂ) * z + u)) / (a * c)) * (ee (d / c * Complex.normSq u) * Φ u) ∂volC =
      ∫ u, ee ((c * Complex.normSq z + -b * Complex.normSq u - 2 * (conj z * u).re) / (-a)) * Φ u ∂volC := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show _ * _ = _ * _
    rw [← mul_assoc, ← ee_add]
    congr 2
    have e1 : Complex.normSq (((-c : ℝ) : ℂ) * z + u) = c ^ 2 * Complex.normSq z + Complex.normSq u - 2 * c * (conj z * u).re := by
      rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
      simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [e1]
    have hb : b = (a * d - 1) / c := by
      field_simp
      linarith
    rw [hb]
    field_simp
    ring
  rw [h1]
  push_cast
  field_simp

theorem rWR_mem {a b c d : ℝ} (h : a * d - b * c = 1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : rWR a b c d Φ ∈ SchC := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    have e : rWR a b 0 d Φ = fun z => (a : ℂ) * (ee (a * b * Complex.normSq z) * Φ ((a : ℂ) * z)) := by
      funext z
      rw [rWR_zero' ha]
      ring
    rw [e]
    exact const_mem _ (chirp_mem _ (dil_mem ha hΦ))
  · have e : rWR a b c d Φ = fun z => (Complex.I * ((-c⁻¹ : ℝ) : ℂ)) * (ee (a / c * Complex.normSq z) *
        Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z)) :=
      funext fun z => rWR_fr' a b d hc Φ z
    rw [e]
    exact const_mem _ (chirp_mem _ (dil_mem (neg_ne_zero.2 (inv_ne_zero hc)) (Fr_mem (chirp_mem _ hΦ))))

def PL (g : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ h : Matrix (Fin 2) (Fin 2) ℝ, h.det = 1 → ∀ Φ ∈ SchC, rWRm (g * h) Φ = rWRm g (rWRm h Φ)

theorem det_eq {h : Matrix (Fin 2) (Fin 2) ℝ} (hd : h.det = 1) : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  rw [← Matrix.det_fin_two]
  exact hd

theorem mem_m {h : Matrix (Fin 2) (Fin 2) ℝ} (hd : h.det = 1) {Φ : ℂ → ℂ} (hΦ : Φ ∈ SchC) : rWRm h Φ ∈ SchC :=
  rWR_mem (det_eq hd) hΦ

theorem PL_n (x : ℝ) : PL !![1, x; 0, 1] := by
  intro h hd Φ _
  funext z
  have := Pn x _ _ _ _ (det_eq hd) Φ z
  simpa [rWRm, Matrix.mul_apply, Fin.sum_univ_two] using this

theorem PL_m {s : ℝ} (hs : s ≠ 0) : PL !![s, 0; 0, s⁻¹] := by
  intro h hd Φ _
  funext z
  have := Pm hs _ _ _ _ (det_eq hd) Φ z
  simpa [rWRm, Matrix.mul_apply, Fin.sum_univ_two, div_eq_inv_mul] using this

theorem PL_w : PL !![0, 1; -1, 0] := by
  intro h hd Φ hΦ
  funext z
  have hdd := det_eq hd
  have e : rWRm (!![0, 1; -1, 0] * h) Φ z = rWR (h 1 0) (h 1 1) (-h 0 0) (-h 0 1) Φ z := by
    simp [rWRm, Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : rWRm !![0, 1; -1, 0] (rWRm h Φ) z = rWR 0 1 (-1) 0 (rWR (h 0 0) (h 0 1) (h 1 0) (h 1 1) Φ) z := by
    simp [rWRm]
  rw [e, e2]
  by_cases hc : h 1 0 = 0
  · rw [hc] at hdd ⊢
    exact Pw0 (by simpa using hdd) Φ z
  · by_cases ha : h 0 0 = 0
    · rw [ha] at hdd ⊢
      simp only [neg_zero]
      exact Pw1 (by linarith) hΦ z
    · exact Pw2 ha hc hdd hΦ z

theorem PL_mul {g g' : Matrix (Fin 2) (Fin 2) ℝ} (hg : PL g) (hg' : PL g') (hd : g'.det = 1) : PL (g * g') := by
  intro h hh Φ hΦ
  rw [Matrix.mul_assoc, hg _ (by rw [Matrix.det_mul, hd, hh, one_mul]) Φ hΦ, hg' h hh Φ hΦ, hg g' hd _ (mem_m hh hΦ)]

theorem PL_all {g : Matrix (Fin 2) (Fin 2) ℝ} (hd : g.det = 1) : PL g := by
  have hdd := det_eq hd
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := by
      intro ha
      rw [ha, hc] at hdd
      simp at hdd
    have hg : g = !![1, g 0 0 * g 0 1; 0, 1] * !![g 0 0, 0; 0, (g 0 0)⁻¹] := by
      rw [hc] at hdd
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc]
      · field_simp
      · field_simp
        linarith
    rw [hg]
    exact PL_mul (PL_n _) (PL_m ha) (by simp [Matrix.det_fin_two, ha])
  · have hg : g = !![1, g 0 0 / g 1 0; 0, 1] * (!![-(g 1 0)⁻¹, 0; 0, (-(g 1 0)⁻¹)⁻¹] * (!![0, 1; -1, 0] * !![1, g 1 1 / g 1 0; 0, 1])) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linarith
    have hs : -(g 1 0)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero hc)
    rw [hg]
    refine PL_mul (PL_n _) (PL_mul (PL_m hs) (PL_mul PL_w (PL_n _) (by simp [Matrix.det_fin_two])) ?_) ?_
    · simp [Matrix.det_fin_two]
    · simp [Matrix.det_fin_two]
      field_simp

theorem rwrrep : RWRREP := fun g h hg hh Φ hΦ => ⟨mem_m hh hΦ, PL_all hg h hh Φ hΦ⟩

end GlobalTheory.CompanionTheory.RealWeil
