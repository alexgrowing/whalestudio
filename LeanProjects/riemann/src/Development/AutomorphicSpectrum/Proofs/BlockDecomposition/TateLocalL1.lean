import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.FunctionalEquationGL2GL1Complex
import GroundTheory.GlobalFields.TateThesis.GaussianComplexFourier

noncomputable section
open MeasureTheory Complex Ad3.K Ad3.K.LC Ad3.K.LC.C
open scoped Real
namespace GlobalTheory.CompanionTheory.TateC

theorem val_measurableEmbedding : MeasurableEmbedding (Units.val : ℂˣ → ℂ) := by
  refine ⟨fun _ _ h => Units.ext h, comap_measurable _, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  have : Units.val '' (Units.val ⁻¹' B : Set ℂˣ) = B ∩ {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, by simp⟩
    · rintro ⟨hx, hx0⟩
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [this]
  exact hB.inter (measurableSet_singleton _).compl

def nuC : Measure ℂ := volume.withDensity fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2)⁻¹

theorem map_val_mulC : Measure.map (Units.val : ℂˣ → ℂ) mulC = nuC := by
  have h := val_measurableEmbedding.map_comap nuC
  have hr : Set.range (Units.val : ℂˣ → ℂ) = {0}ᶜ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      simp
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  have hac : nuC ≪ volume := withDensity_absolutelyContinuous _ _
  have h0 : nuC {0} = 0 := hac (by simp)
  have : nuC.restrict ({0}ᶜ : Set ℂ) = nuC :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]
      simpa using h0)
  rw [hr, this] at h
  exact h

theorem integral_mulC (F : ℂ → ℂ) :
    ∫ a : ℂˣ, F a ∂mulC = ∫ x : ℂ, (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * F x := by
  have h1 : ∫ a : ℂˣ, F a ∂mulC = ∫ x, F x ∂nuC := by
    rw [← map_val_mulC, val_measurableEmbedding.integral_map]
  rw [h1, nuC, integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : 0 ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  simp only [ENNReal.toReal_ofReal this, Complex.real_smul]

theorem integrable_mulC_iff (g : ℂ → ℂ) :
    Integrable (fun a : ℂˣ => g a) mulC ↔ Integrable (fun x : ℂ => (‖x‖ ^ 2)⁻¹ • g x) volume := by
  have hE := val_measurableEmbedding
  have hd : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ 2)⁻¹ := by fun_prop
  have h2 : Integrable (fun a : ℂˣ => g a) mulC ↔
      Integrable g (Measure.map (Units.val : ℂˣ → ℂ) mulC) :=
    (hE.integrable_map_iff (g := g)).symm
  rw [h2, map_val_mulC, nuC,
    integrable_withDensity_iff_integrable_smul' hd (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  have : 0 ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  simp only [ENNReal.toReal_ofReal this]

instance : SigmaFinite mulC := by
  refine SigmaFinite.of_map _ val_measurableEmbedding.measurable.aemeasurable ?_
  rw [map_val_mulC, nuC]
  exact SigmaFinite.withDensity_ofReal _

theorem map_mul_volume {g : ℂ} (hg : g ≠ 0) :
    Measure.map (fun x : ℂ => x * g) volume = ENNReal.ofReal (‖g‖ ^ 2)⁻¹ • volume := by
  have hd : LinearMap.det (Algebra.lmul ℝ ℂ g) = ‖g‖ ^ 2 := by
    have := Algebra.norm_complex_apply g
    rw [Algebra.norm_apply] at this
    rw [Complex.normSq_eq_norm_sq] at this
    exact this
  have hne : LinearMap.det (Algebra.lmul ℝ ℂ g) ≠ 0 := by
    rw [hd]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 hg)
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne
  have hf : (⇑(Algebra.lmul ℝ ℂ g) : ℂ → ℂ) = fun x : ℂ => x * g := by
    funext x
    simp [mul_comm]
  rw [hf, hd, abs_of_nonneg (by positivity)] at h
  exact h

theorem nuC_preimage {g : ℂ} (hg : g ≠ 0) {B : Set ℂ} (hB : MeasurableSet B) :
    nuC ((fun x => x * g) ⁻¹' B) = nuC B := by
  have hw : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ 2)⁻¹ := by fun_prop
  have hm : Measurable fun x : ℂ => x * g := by fun_prop
  have hgn : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hg)
  have hgp : 0 ≤ ‖g‖ ^ 2 := by positivity
  set w : ℂ → ENNReal := fun x : ℂ => ENNReal.ofReal (‖x‖ ^ 2)⁻¹ with hwdef
  have h1 : ∀ x, ((fun x => x * g) ⁻¹' B).indicator w x
      = ENNReal.ofReal (‖g‖ ^ 2) * (B.indicator w) (x * g) := by
    intro x
    by_cases hx : x * g ∈ B
    · rw [Set.indicator_of_mem (show x ∈ (fun x => x * g) ⁻¹' B from hx), Set.indicator_of_mem hx,
        hwdef]
      simp only
      rw [← ENNReal.ofReal_mul hgp]
      congr 1
      rw [norm_mul, mul_pow, mul_inv, mul_comm ((‖x‖ ^ 2)⁻¹), ← mul_assoc,
        mul_inv_cancel₀ hgn, one_mul]
    · rw [Set.indicator_of_notMem (show x ∉ (fun x => x * g) ⁻¹' B from hx),
        Set.indicator_of_notMem hx]
      simp
  have hmeas : Measurable fun x : ℂ => B.indicator w (x * g) := (hw.indicator hB).comp hm
  rw [nuC, withDensity_apply _ (hm hB), withDensity_apply _ hB, ← lintegral_indicator (hm hB),
    ← lintegral_indicator hB, lintegral_congr h1, lintegral_const_mul _ hmeas]
  have h2 : ∫⁻ x, B.indicator w (x * g)
      = ∫⁻ y, B.indicator w y ∂(Measure.map (fun x => x * g) volume) :=
    (lintegral_map (hw.indicator hB) hm).symm
  rw [h2, map_mul_volume hg, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hgp, mul_inv_cancel₀ hgn]
  simp only [ENNReal.ofReal_one, one_mul]
  rfl

instance : mulC.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  ext A hA
  obtain ⟨B, hB, rfl⟩ := hA
  have hpre : ∀ C : Set ℂ, MeasurableSet C → mulC (Units.val ⁻¹' C) = nuC C := by
    intro C hC
    rw [← map_val_mulC, Measure.map_apply val_measurableEmbedding.measurable hC]
  have hm : Measurable fun x : ℂˣ => x * g := measurable_mul_const g
  rw [Measure.map_apply hm (val_measurableEmbedding.measurable hB), hpre B hB]
  have : (fun x : ℂˣ => x * g) ⁻¹' (Units.val ⁻¹' B)
      = Units.val ⁻¹' ((fun x : ℂ => x * (g : ℂ)) ⁻¹' B) := by
    ext x
    simp
  rw [this, hpre _ ((measurable_mul_const (g : ℂ)) hB), nuC_preimage g.ne_zero hB]

def cF (n : ℤ) (s : ℂ) (x : ℂ) : ℂ := (x / (‖x‖ : ℂ)) ^ n * ((‖x‖ ^ 2 : ℝ) : ℂ) ^ s

theorem measurable_zpow (n : ℤ) : Measurable fun x : ℂ => x ^ n := by
  cases n with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact measurable_id.pow_const k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (measurable_id.pow_const _).inv

theorem measurable_cF (n : ℤ) (s : ℂ) : Measurable (cF n s) := by
  unfold cF
  have h1 : Measurable fun x : ℂ => x / (‖x‖ : ℂ) :=
    measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)
  exact ((measurable_zpow n).comp h1).mul
    ((Complex.measurable_ofReal.comp (measurable_norm.pow_const 2)).pow_const s)

theorem norm_cF {x : ℂ} (hx : x ≠ 0) (n : ℤ) (s : ℂ) : ‖cF n s x‖ = (‖x‖ ^ 2) ^ s.re := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hp : 0 < ‖x‖ ^ 2 := by positivity
  have h1 : ‖x / (‖x‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hn]
  rw [cF, norm_mul, norm_zpow, h1, one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp]

theorem integrable_chC (F : ℂ → ℂ) (n : ℤ) (s : ℂ) (hm : AEStronglyMeasurable F volume)
    (h : Integrable (fun x : ℂ => F x * ((‖x‖ ^ (2 * (s.re - 1)) : ℝ) : ℂ))) :
    Integrable (fun a : ℂˣ => F a * chC n s a) mulC := by
  have key : Integrable (fun x : ℂ => (‖x‖ ^ 2)⁻¹ • (F x * cF n s x)) volume := by
    have hm' : AEStronglyMeasurable (fun x : ℂ => (‖x‖ ^ 2)⁻¹ • (F x * cF n s x)) volume :=
      ((measurable_norm.pow_const 2).inv).aestronglyMeasurable.smul
        (hm.mul (measurable_cF n s).aestronglyMeasurable)
    refine h.mono hm' ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with x hx
    have hx0 : x ≠ 0 := hx
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hp2 : 0 < ‖x‖ ^ 2 := by positivity
    have hw : ‖x‖ ^ (2 * (s.re - 1)) = (‖x‖ ^ 2)⁻¹ * (‖x‖ ^ 2) ^ s.re := by
      rw [Real.rpow_mul hpos.le, Real.rpow_two, Real.rpow_sub_one hp2.ne']
      field_simp
    have hnn : 0 ≤ ‖x‖ ^ (2 * (s.re - 1)) := Real.rpow_nonneg hpos.le _
    rw [norm_smul, norm_mul, norm_cF hx0, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn,
      Real.norm_of_nonneg (by positivity), hw]
    exact le_of_eq (by ring)
  exact (integrable_mulC_iff (fun x => F x * cF n s x)).2 key

theorem chC_mul (n : ℤ) (s : ℂ) (t b : ℂˣ) :
    chC (-n) (1 - s) (t * b) * chC n s b = chC (-n) (1 - s) t * ((‖(b : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have hbn : ‖(b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 b.ne_zero
  have hb0 : ((‖(b : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (pow_ne_zero _ hbn)
  have hu : (b : ℂ) / (‖(b : ℂ)‖ : ℂ) ≠ 0 :=
    div_ne_zero b.ne_zero (Complex.ofReal_ne_zero.2 hbn)
  have hang : (((t * b : ℂˣ) : ℂ) / (‖((t * b : ℂˣ) : ℂ)‖ : ℂ)) ^ (-n)
      * ((b : ℂ) / (‖(b : ℂ)‖ : ℂ)) ^ n = ((t : ℂ) / (‖(t : ℂ)‖ : ℂ)) ^ (-n) := by
    have h : ((t * b : ℂˣ) : ℂ) / (‖((t * b : ℂˣ) : ℂ)‖ : ℂ)
        = ((t : ℂ) / (‖(t : ℂ)‖ : ℂ)) * ((b : ℂ) / (‖(b : ℂ)‖ : ℂ)) := by
      rw [Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
    rw [h, mul_zpow, mul_assoc, zpow_neg ((b : ℂ) / (‖(b : ℂ)‖ : ℂ)),
      inv_mul_cancel₀ (zpow_ne_zero n hu), mul_one]
  have hpow : ((‖((t * b : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (1 - s) * ((‖(b : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s
      = ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (1 - s) * ((‖(b : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Units.val_mul, norm_mul, mul_pow, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), mul_assoc,
      ← Complex.cpow_add _ _ hb0]
    simp
  simp only [chC]
  calc _ = ((((t * b : ℂˣ) : ℂ) / (‖((t * b : ℂˣ) : ℂ)‖ : ℂ)) ^ (-n)
        * ((b : ℂ) / (‖(b : ℂ)‖ : ℂ)) ^ n)
      * (((‖((t * b : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (1 - s) * ((‖(b : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s) := by ring
    _ = _ := by rw [hang, hpow]; ring

theorem tate_zeta_product (F G : ℂ → ℂ) (n : ℤ) (s : ℂ)
    (hF : Integrable (fun a : ℂˣ => F a * chC (-n) (1 - s) a) mulC)
    (hG : Integrable (fun a : ℂˣ => G a * chC n s a) mulC) :
    z1 F (-n) (1 - s) * z1 G n s
      = ∫ t : ℂˣ, chC (-n) (1 - s) t * (∫ x : ℂ, G x * F (t * x)) ∂mulC := by
  set A : ℂˣ → ℂ := fun a => F a * chC (-n) (1 - s) a with hA
  set B : ℂˣ → ℂ := fun a => G a * chC n s a with hB
  have hP : Integrable (fun p : ℂˣ × ℂˣ => A p.1 * B p.2) (mulC.prod mulC) := hF.mul_prod hG
  have hT := measurePreserving_mul_prod (mulC) (mulC)
  have hP' : Integrable (fun p : ℂˣ × ℂˣ => A (p.1 * p.2) * B p.2) (mulC.prod mulC) :=
    hT.integrable_comp_of_integrable hP
  have h1 : z1 F (-n) (1 - s) * z1 G n s = ∫ b, ∫ t, A (t * b) * B b ∂mulC ∂mulC := by
    change (∫ a, A a ∂mulC) * (∫ b, B b ∂mulC) = _
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only
    rw [integral_mul_const, integral_mul_right_eq_self A b]
  rw [h1, ← integral_integral_swap (f := fun t b => A (t * b) * B b) hP']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have h2 : ∀ b : ℂˣ, A (t * b) * B b
      = chC (-n) (1 - s) t * (((‖(b : ℂ)‖ ^ 2 : ℝ) : ℂ) * (G b * F (t * b))) := by
    intro b
    have := chC_mul n s t b
    simp only [hA, hB, Units.val_mul]
    calc _ = F (t * b) * G b * (chC (-n) (1 - s) (t * b) * chC n s b) := by
          ring
      _ = _ := by rw [this]; ring
  simp only [h2]
  rw [integral_const_mul]
  congr 1
  rw [integral_mulC (fun x : ℂ => ((‖x‖ ^ 2 : ℝ) : ℂ) * (G x * F (t * x)))]
  refine integral_congr_ae ?_
  have h0 : ∀ᵐ x : ℂ, x ≠ 0 := by simp [ae_iff]
  filter_upwards [h0] with x hx
  have : (((‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((‖x‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hx))]
    simp
  rw [← mul_assoc, this, one_mul]

theorem psi_coe (x : ℂ) : ((Real.fourierChar (-(2 * x.re)) : Circle) : ℂ) = psiC x := by
  rw [Real.fourierChar_apply, psiC]
  congr 1
  push_cast
  ring

theorem fC_eq_two_mul (h : ℂ → ℂ) (w : ℂ) : fC h w = 2 * ∫ z, h z * psiC (z * w) := by
  rw [fC, volC, integral_smul_measure]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]

def bil (t : ℂ) : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => 2 * (t * x * y).re)
    (fun a b y => by simp only [mul_add, add_mul, Complex.add_re])
    (fun c x y => by
      simp only [Complex.real_smul, smul_eq_mul]
      rw [show t * ((c : ℂ) * x) * y = (c : ℂ) * (t * x * y) by ring, Complex.re_ofReal_mul]
      ring)
    (fun x a b => by simp only [mul_add, Complex.add_re])
    (fun c x y => by
      simp only [Complex.real_smul, smul_eq_mul]
      rw [show t * x * ((c : ℂ) * y) = (c : ℂ) * (t * x * y) by ring, Complex.re_ofReal_mul]
      ring)

theorem bil_apply (t x y : ℂ) : bil t x y = 2 * (t * x * y).re := rfl

theorem fC_scaled_swap (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) (t : ℂ) :
    ∫ x : ℂ, g x * fC f (t * x) = ∫ x : ℂ, f x * fC g (t * x) := by
  have hL : Continuous fun p : ℂ × ℂ => bil t p.1 p.2 := by
    simp only [bil_apply]
    exact continuous_const.mul (Complex.continuous_re.comp (by fun_prop))
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ)) (L := bil t)
    (f := f) (g := g) Real.continuous_fourierChar hL hf hg
  have hF : ∀ (h : ℂ → ℂ) (y : ℂ), fC h (t * y)
      = 2 * VectorFourier.fourierIntegral Real.fourierChar volume (bil t) h y := by
    intro h y
    rw [fC_eq_two_mul, VectorFourier.fourierIntegral]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [bil_apply, Circle.smul_def, psi_coe, smul_eq_mul]
    rw [mul_comm, show v * (t * y) = t * v * y by ring]
  have hF' : ∀ (h : ℂ → ℂ) (y : ℂ), fC h (t * y)
      = 2 * VectorFourier.fourierIntegral Real.fourierChar volume (bil t).flip h y := by
    intro h y
    rw [fC_eq_two_mul, VectorFourier.fourierIntegral]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [LinearMap.flip_apply, bil_apply, Circle.smul_def, psi_coe, smul_eq_mul]
    rw [mul_comm, show v * (t * y) = t * y * v by ring]
  simp only [hF f, hF' g]
  simp only [smul_eq_mul] at key
  calc _ = 2 * ∫ x, VectorFourier.fourierIntegral Real.fourierChar volume (bil t) f x * g x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        ring
    _ = 2 * ∫ x, f x * VectorFourier.fourierIntegral Real.fourierChar volume (bil t).flip g x := by
        rw [key]
    _ = _ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        ring

theorem tate_zeta_symmetric (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) (n : ℤ) (s : ℂ)
    (A : Integrable (fun a : ℂˣ => fC f a * chC (-n) (1 - s) a) mulC)
    (B : Integrable (fun a : ℂˣ => f a * chC n s a) mulC)
    (C : Integrable (fun a : ℂˣ => fC g a * chC (-n) (1 - s) a) mulC)
    (D : Integrable (fun a : ℂˣ => g a * chC n s a) mulC) :
    z1 (fC f) (-n) (1 - s) * z1 g n s = z1 (fC g) (-n) (1 - s) * z1 f n s := by
  rw [tate_zeta_product _ _ n s A D, tate_zeta_product _ _ n s C B]
  simp only [fC_scaled_swap f g hf hg]

theorem continuous_gauss (m : ℤ) : Continuous (GroundTheory.Global.complexGaussian m) := by
  unfold GroundTheory.Global.complexGaussian
  split_ifs <;> fun_prop

theorem integrable_gauss (m : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : ℂ => GroundTheory.Global.complexGaussian m x * ((‖x‖ ^ (2 * (σ - 1)) : ℝ) : ℂ)) := by
  have h : Integrable (fun z : ℂ => (fun y : ℝ =>
      y ^ m.natAbs * Real.exp (-(2 * π) * y ^ 2) * y ^ (2 * (σ - 1))) ‖z‖) := by
    refine (integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := fun y : ℝ => y ^ m.natAbs * Real.exp (-(2 * π) * y ^ 2) * y ^ (2 * (σ - 1)))).2 ?_
    rw [Complex.finrank_real_complex]
    have h2 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 2 * π) (by positivity)
      (s := (m.natAbs : ℝ) + 2 * σ - 1) (by
        have := Nat.cast_nonneg (α := ℝ) m.natAbs
        linarith)
    refine h2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := hy
    have e2 : (m.natAbs : ℝ) + 2 * σ - 1 = 1 + ((m.natAbs : ℝ) + 2 * (σ - 1)) := by ring
    show y ^ ((m.natAbs : ℝ) + 2 * σ - 1) * Real.exp (-(2 * π) * y ^ 2) = _
    rw [e2, Real.rpow_add hy0, Real.rpow_add hy0, Real.rpow_one, Real.rpow_natCast]
    simp only [smul_eq_mul, Nat.add_one_sub_one, pow_one]
    ring
  refine h.mono' ?_ ?_
  · exact (continuous_gauss m).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (measurable_norm.pow_const _)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have hnn : 0 ≤ ‖z‖ ^ (2 * (σ - 1)) := Real.rpow_nonneg (norm_nonneg _) _
    have hre : (-2 * π * (‖z‖ : ℂ) ^ 2).re = -(2 * π) * ‖z‖ ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    have hp : ‖(if 0 ≤ m then z ^ m.natAbs else (starRingEnd ℂ) z ^ m.natAbs)‖ = ‖z‖ ^ m.natAbs := by
      split_ifs <;> simp
    rw [norm_mul, GroundTheory.Global.complexGaussian, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_of_nonneg hnn, hp, hre]

theorem tate_zeta_gaussian (m : ℤ) {s : ℂ} (hs : 0 < s.re) :
    z1 (GroundTheory.Global.complexGaussian m) (-m) s = π / 2 * Gammaℂ (s + m.natAbs / 2) := by
  have h := GroundTheory.Global.integral_complexGaussian_mul_zpow_mul_cpow m (s := s) (by
    have := Nat.cast_nonneg (α := ℝ) m.natAbs
    linarith)
  rw [GroundTheory.Global.complexPlaceMeasure, integral_smul_measure, ENNReal.toReal_ofNat,
    Complex.real_smul] at h
  have e : z1 (GroundTheory.Global.complexGaussian m) (-m) s
      = ∫ z : ℂ, GroundTheory.Global.complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) *
          ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    refine (integral_mulC (fun x => GroundTheory.Global.complexGaussian m x * cF (-m) s x)).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [cF, Complex.ofReal_inv]
    rw [div_eq_mul_inv]
    ring
  rw [e]
  generalize (∫ z : ℂ, GroundTheory.Global.complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) *
          ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ)) = J at h ⊢
  push_cast at h
  linear_combination (1 / 2 : ℂ) * h

theorem gammaC_ne {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  rw [Ne, Complex.cpow_eq_zero_iff]
  simp [Real.pi_ne_zero]

theorem tate_zeta_const_mul (c : ℂ) (G : ℂ → ℂ) (n : ℤ) (s : ℂ) :
    z1 (fun w => c * G w) n s = c * z1 G n s := by
  simp only [z1, mul_assoc]
  exact integral_const_mul _ _

theorem fC_eq_complexFourier (h : ℂ → ℂ) : fC h = GroundTheory.Global.complexFourier h := by
  funext w
  have hv : volC = GroundTheory.Global.complexPlaceMeasure := rfl
  rw [fC, GroundTheory.Global.complexFourier, hv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Circle.smul_def, psi_coe, smul_eq_mul]
  rw [mul_comm]

theorem fC_gauss (n : ℤ) : fC (GroundTheory.Global.complexGaussian (-n))
    = fun w => (-Complex.I) ^ n.natAbs * GroundTheory.Global.complexGaussian n w := by
  rw [fC_eq_complexFourier, GroundTheory.Global.complexFourier_complexGaussian]
  simp only [Int.natAbs_neg, neg_neg]

theorem continuous_fC {f : ℂ → ℂ} (hf : Integrable f) : Continuous (fC f) := by
  rw [fC_eq_complexFourier, GroundTheory.Global.complexFourier_eq_fourierIntegral]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    GroundTheory.Global.traceFormℂ.continuous₂ (hf.smul_measure (by simp))

theorem main : TateFunctionalEquationComplex := by
  intro f n s h0 h1 hf hw hF
  have h1' : 0 < (1 - s).re := by simpa using h1
  have hG : Integrable (GroundTheory.Global.complexGaussian (-n)) := by
    simpa using GroundTheory.Global.integrable_norm_pow_smul_complexGaussian (-n) 0
  have A : Integrable (fun a : ℂˣ => fC f a * chC (-n) (1 - s) a) mulC := by
    refine integrable_chC _ _ _ (continuous_fC hf).aestronglyMeasurable ?_
    have e : 2 * ((1 - s).re - 1) = -2 * s.re := by
      simp only [Complex.sub_re, Complex.one_re]
      ring
    rw [e]
    exact hF
  have B := integrable_chC f n s hf.aestronglyMeasurable hw
  have C : Integrable (fun a : ℂˣ => fC (GroundTheory.Global.complexGaussian (-n)) a
      * chC (-n) (1 - s) a) mulC := by
    refine integrable_chC _ _ _ (continuous_fC hG).aestronglyMeasurable ?_
    rw [fC_gauss]
    simp only [mul_assoc]
    exact (integrable_gauss n h1').const_mul _
  have D := integrable_chC _ n s (continuous_gauss (-n)).aestronglyMeasurable
    (integrable_gauss (-n) h0)
  have key := tate_zeta_symmetric f _ hf hG n s A B C D
  have g0 := tate_zeta_gaussian (-n) h0
  rw [neg_neg, Int.natAbs_neg] at g0
  rw [fC_gauss, tate_zeta_const_mul, tate_zeta_gaussian n h1', g0] at key
  have hne : Gammaℂ (s + n.natAbs / 2) ≠ 0 := by
    refine gammaC_ne ?_
    have : (0 : ℝ) ≤ n.natAbs := Nat.cast_nonneg _
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    positivity
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [gC]
  generalize Gammaℂ (s + n.natAbs / 2) = G0 at key hne ⊢
  generalize Gammaℂ (1 - s + n.natAbs / 2) = G1 at key ⊢
  generalize z1 (fC f) (-n) (1 - s) = Z1 at key ⊢
  generalize z1 f n s = Z0 at key ⊢
  generalize (-Complex.I) ^ n.natAbs = c at key ⊢
  have hp2 : (π : ℂ) / 2 * G0 ≠ 0 := mul_ne_zero (div_ne_zero hpi two_ne_zero) hne
  apply mul_right_cancel₀ hp2
  rw [key]
  field_simp

end GlobalTheory.CompanionTheory.TateC
