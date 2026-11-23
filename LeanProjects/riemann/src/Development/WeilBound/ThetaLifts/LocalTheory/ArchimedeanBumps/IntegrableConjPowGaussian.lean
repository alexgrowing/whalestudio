import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ExistsDensity
import GroundTheory.GlobalFields.TateThesis.GaussianComplexFourier

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

variable {ι : Type} [Fintype ι]

def nm (y : ι → ℂ) : ℝ := ∏ w, ‖y w‖ ^ 2

theorem nm_pos {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) : 0 < nm y := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hy w)) 2

theorem nm_mul (x y : ι → ℂ) : nm (x * y) = nm x * nm y := by simp [nm, mul_pow, Finset.prod_mul_distrib]

theorem nm_inv (x : ι → ℂ) : nm x⁻¹ = (nm x)⁻¹ := by simp [nm, Finset.prod_inv_distrib]

theorem continuous_nm : Continuous (nm : (ι → ℂ) → ℝ) := by unfold nm; fun_prop

theorem ae_unit : ∀ᵐ y : ι → ℂ, ∀ w, y w ≠ 0 := ae_all_iff.2 fun w => Measure.ae_eval_ne (fun _ : ι => (volume : Measure ℂ)) w 0

theorem map_mul_volume_pi_complex {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) :
    Measure.map (fun x : ι → ℂ => y * x) volume = ENNReal.ofReal (nm y)⁻¹ • volume := by
  classical
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun w => (Algebra.lmul ℝ ℂ (y w)).comp (LinearMap.proj w)
  have hd : LinearMap.det L = nm y := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := L) (by rw [hd]; exact (nm_pos hy).ne')
  rw [hd, abs_of_pos (inv_pos.2 (nm_pos hy))] at this
  exact this

theorem meas_mul (y : ι → ℂ) : Measurable fun x : ι → ℂ => y * x := (continuous_const.mul continuous_id).measurable

theorem integral_scale {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → E}
    (hg : AEStronglyMeasurable g volume) : ∫ x, g (y * x) = (nm y)⁻¹ • ∫ x, g x := by
  rw [← integral_map (meas_mul y).aemeasurable (by rw [map_mul_volume_pi_complex hy]; exact hg.smul_measure _), map_mul_volume_pi_complex hy,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 (nm_pos hy)).le]

theorem integrable_scale {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) {g : (ι → ℂ) → ℂ} (hg : Integrable g) : Integrable fun x => g (y * x) := by
  have : Integrable g (Measure.map (fun x : ι → ℂ => y * x) volume) := by
    rw [map_mul_volume_pi_complex hy]; exact hg.smul_measure ENNReal.ofReal_ne_top
  exact this.comp_measurable (meas_mul y)

theorem kernel {a j : (ι → ℂ) → ℂ} (ha : AEStronglyMeasurable a volume) (hj : Integrable j) (hjm : Measurable j) {s : (ι → ℂ) → ι → ℂ}
    (hs : Measurable s) (hsU : ∀ x, (∀ w, x w ≠ 0) → ∀ w, s x w ≠ 0) (hi : Integrable fun x => a x * ((nm (s x) : ℝ) : ℂ)⁻¹) :
    Integrable (fun q : (ι → ℂ) × (ι → ℂ) => a q.1 * j (s q.1 * q.2)) (volume.prod volume) ∧
      ∫ x, ∫ y, a x * j (s x * y) = (∫ x, a x * ((nm (s x) : ℝ) : ℂ)⁻¹) * ∫ y, j y := by
  constructor
  · have hm : AEStronglyMeasurable (fun q : (ι → ℂ) × (ι → ℂ) => a q.1 * j (s q.1 * q.2)) (volume.prod volume) :=
      ha.comp_fst.mul (hjm.comp ((hs.comp measurable_fst).mul measurable_snd)).aestronglyMeasurable
    refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
    · filter_upwards [ae_unit] with x hx using (integrable_scale (hsU x hx) hj).const_mul _
    · refine (hi.norm.mul_const (∫ y, ‖j y‖)).congr ?_
      filter_upwards [ae_unit] with x hx
      simp only [norm_mul]
      rw [integral_const_mul, integral_scale (hsU x hx) (g := fun y => ‖j y‖) hj.1.norm, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (nm_pos (hsU x hx)).le, smul_eq_mul, mul_assoc]
  · rw [← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [ae_unit] with x hx
    rw [integral_const_mul, integral_scale (hsU x hx) hj.1, Complex.real_smul, mul_assoc]
    push_cast; rfl

def pr (x y : ι → ℂ) : ℝ := ∑ w, 2 * (x w * y w).re

theorem continuous_pr : Continuous fun q : (ι → ℂ) × (ι → ℂ) => pr q.1 q.2 := by unfold pr; fun_prop

def FT (h : (ι → ℂ) → ℂ) (t : ι → ℂ) : ℂ := ∫ x, ch (-pr x t) * h x

theorem continuous_FT {h : (ι → ℂ) → ℂ} (hh : Integrable h) : Continuous (FT h) := by
  refine continuous_of_dominated (bound := fun x => ‖h x‖) (fun t => ?_) (fun t => Eventually.of_forall fun x => ?_) hh.norm
    (Eventually.of_forall fun x => ?_)
  · exact (continuous_ch.comp (continuous_pr.comp (continuous_id.prodMk continuous_const)).neg).aestronglyMeasurable.mul hh.1
  · rw [norm_mul, norm_ch, one_mul]
  · exact (continuous_ch.comp (continuous_pr.comp (continuous_const.prodMk continuous_id)).neg).mul continuous_const

theorem pr_comm (x y : ι → ℂ) : pr x y = pr y x := by simp [pr, mul_comm]

theorem FT_mul {h m : (ι → ℂ) → ℂ} (hh : Integrable h) (hm : Integrable m) : ∫ t, FT h t * m t = ∫ x, h x * FT m x := by
  have hi : Integrable (fun q : (ι → ℂ) × (ι → ℂ) => ch (-pr q.2 q.1) * (m q.1 * h q.2)) (volume.prod volume) := by
    refine (hm.mul_prod hh).bdd_mul (c := 1) ?_ (Eventually.of_forall fun q => (norm_ch _).le)
    exact (continuous_ch.comp (continuous_pr.comp continuous_swap).neg).aestronglyMeasurable
  calc ∫ t, FT h t * m t = ∫ t, ∫ x, ch (-pr x t) * (m t * h x) := by
        congr 1; funext t; rw [FT, ← integral_mul_const]; congr 1; funext x; ring
    _ = ∫ x, ∫ t, ch (-pr x t) * (m t * h x) := integral_integral_swap hi
    _ = _ := by
        congr 1; funext x; rw [FT, ← integral_const_mul]; congr 1; funext t; rw [pr_comm]; ring

theorem FT_scale {m : (ι → ℂ) → ℂ} (hm : Integrable m) {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) (x : ι → ℂ) :
    FT (fun t => m (y * t)) x = ((nm y : ℝ) : ℂ)⁻¹ * FT m (x * y⁻¹) := by
  have h := integral_scale hy (g := fun t => ch (-pr t (x * y⁻¹)) * m t)
    ((continuous_ch.comp (continuous_pr.comp (continuous_id.prodMk continuous_const)).neg).aestronglyMeasurable.mul hm.1)
  rw [Complex.real_smul] at h
  push_cast at h
  rw [FT, FT, ← h]
  congr 1; funext t; congr 3
  refine Finset.sum_congr rfl fun w _ => ?_
  have := hy w
  simp only [Pi.mul_apply, Pi.inv_apply]
  congr 2; field_simp

def r0 (κ : ι → ℕ) (e : ℕ) (x : ι → ℂ) : ℂ := ∏ w, (x w / (‖x w‖ : ℂ)) ^ κ w * (‖x w‖ : ℂ) ^ (2 * e)

theorem rationalWeight_mul (κ : ι → ℕ) (e : ℕ) (x y : ι → ℂ) : r0 κ e (x * y) = r0 κ e x * r0 κ e y := by
  rw [r0, r0, r0, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp only [Pi.mul_apply, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_pow]; ring

theorem rationalWeight_ne_zero (κ : ι → ℕ) (e : ℕ) {x : ι → ℂ} (hx : ∀ w, x w ≠ 0) : r0 κ e x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun w _ => by have := hx w; simp [this]

theorem measurable_reduced_size (κ : ι → ℕ) (e : ℕ) : Measurable (r0 κ e) := by unfold r0; fun_prop

theorem rationalWeight_one (κ : ι → ℕ) (e : ℕ) : r0 κ e 1 = 1 := by simp [r0]

def gm (κ : ι → ℕ) (x : ι → ℂ) : ℂ := ∏ w, conj (x w) ^ κ w * Complex.exp (-2 * Real.pi * (‖x w‖ : ℂ) ^ 2)

theorem norm_gauss (z : ℂ) : ‖Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2)‖ = Real.exp (-2 * Real.pi * ‖z‖ ^ 2) := by
  have : (-2 * Real.pi * (‖z‖ : ℂ) ^ 2 : ℂ) = ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal]

theorem poly_le (t : ℝ) (ht : 0 ≤ t) (s : ℕ) : (1 + t) ^ s * Real.exp (-2 * Real.pi * t ^ 2) ≤ Real.exp (s ^ 2) := by
  have h1 : (1 + t) ^ s ≤ Real.exp (s * t) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) s
  calc _ ≤ Real.exp (s * t) * Real.exp (-2 * Real.pi * t ^ 2) := by gcongr
    _ ≤ _ := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2
      nlinarith [Real.pi_gt_three, sq_nonneg (t - s), sq_nonneg t, sq_nonneg (s : ℝ)]

theorem int_of_le {g : ℂ → ℂ} (hg : Measurable g) (C : ℝ) (h : ∀ z, z ≠ 0 → ‖g z‖ * (1 + ‖z‖) ^ 3 ≤ C) : Integrable g := by
  have h3 : Integrable fun z : ℂ => (1 + ‖z‖) ^ (-(3 : ℝ)) := integrable_one_add_norm (by simp; norm_num)
  refine (h3.const_mul C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
  have hp : 0 < (1 + ‖z‖) ^ 3 := by positivity
  rw [Real.rpow_neg (by positivity), show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
  exact h z hz

theorem int_pg {g : ℂ → ℂ} (hg : Measurable g) (s : ℕ) (h : ∀ z, ‖g z‖ ≤ ‖z‖ ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2)) : Integrable g := by
  refine int_of_le hg (Real.exp ((s + 3 : ℕ) ^ 2)) fun z _ => le_trans ?_ (poly_le ‖z‖ (norm_nonneg z) (s + 3))
  have : ‖z‖ ^ s ≤ (1 + ‖z‖) ^ s := pow_le_pow_left₀ (norm_nonneg z) (by linarith) s
  calc _ ≤ (1 + ‖z‖) ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) * (1 + ‖z‖) ^ 3 := by
        gcongr; exact (h z).trans (by gcongr)
    _ = _ := by ring

theorem integrable_conj_pow_gaussian (k : ℕ) : Integrable fun z : ℂ => conj z ^ k * Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2) :=
  int_pg (by fun_prop) k fun z => by rw [norm_mul, norm_gauss, norm_pow, Complex.norm_conj]

theorem integrable_gm (κ : ι → ℕ) : Integrable (gm κ) := by
  have := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) fun w => integrable_conj_pow_gaussian (κ w)
  exact this

theorem ch_sum (f : ι → ℝ) : ch (∑ w, f w) = ∏ w, ch (f w) := by
  simp only [ch]; rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.mul_sum]

theorem FT_gm (κ : ι → ℕ) (x : ι → ℂ) :
    FT (gm κ) x = ∏ w, (2⁻¹ * (-Complex.I) ^ κ w) * (x w ^ κ w * Complex.exp (-2 * Real.pi * (‖x w‖ : ℂ) ^ 2)) := by
  have h1 : FT (gm κ) x = ∏ w, ∫ z : ℂ, ch (-(2 * (z * x w).re)) * (conj z ^ κ w * Complex.exp (-2 * Real.pi * (‖z‖ : ℂ) ^ 2)) := by
    rw [← integral_fintype_prod_volume_eq_prod, FT]
    congr 1; funext t
    rw [pr, ← Finset.sum_neg_distrib, ch_sum, gm, ← Finset.prod_mul_distrib]
  rw [h1]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h := congrFun (GroundTheory.Global.complexFourier_conj_pow_mul_gaussian (κ w)) (x w)
  rw [GroundTheory.Global.complexFourier, GroundTheory.Global.complexPlaceMeasure, integral_smul_measure] at h
  rw [mul_assoc, ← h]
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ two_ne_zero, one_mul]
  congr 1; funext z; congr 1
  rw [ch]; congr 1; push_cast; ring

theorem tate (κ : ι → ℕ) (e : ℕ) (hκ : ∀ w, 2 * e < κ w) : ∃ Z : ℂ, ∀ H : (ι → ℂ) → ℂ, Integrable H →
    Integrable (fun x => H x * r0 κ e x) → Integrable (fun t => FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹)) →
    ∫ t, FT H t * ((r0 κ e t)⁻¹ * ((nm t : ℝ) : ℂ)⁻¹) = Z * ∫ x, H x * r0 κ e x := by
  let j₁ : (ι → ℂ) → ℂ := fun y => gm κ y * r0 κ e y
  let j₂ : (ι → ℂ) → ℂ := fun y => FT (gm κ) y⁻¹ * r0 κ e y * ((nm y : ℝ) : ℂ)⁻¹
  have e₁ : j₁ = fun y => ∏ w, ((‖y w‖ ^ (κ w + 2 * e) * Real.exp (-2 * Real.pi * ‖y w‖ ^ 2) : ℝ) : ℂ) := by
    funext y
    simp only [j₁, gm, r0]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hk : κ w ≠ 0 := by have := hκ w; omega
    by_cases hy : y w = 0
    · simp [hy, hk]
    · have hn : (‖y w‖ : ℂ) ≠ 0 := by simpa using hy
      have : conj (y w) * (y w / ‖y w‖) = ‖y w‖ := by
        rw [← mul_div_assoc, Complex.conj_mul', div_eq_iff hn]; ring
      push_cast
      calc _ = (conj (y w) * (y w / ‖y w‖)) ^ κ w * (‖y w‖ : ℂ) ^ (2 * e) * Complex.exp (-2 * Real.pi * (‖y w‖ : ℂ) ^ 2) := by
            rw [mul_pow]; ring
        _ = _ := by rw [this, pow_add]
  have i1 : ∀ s : ℕ, Integrable fun z : ℂ => ((‖z‖ ^ s * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ) := fun s =>
    int_pg (by fun_prop) s fun z => by rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hj₁ : Integrable j₁ := by
    rw [e₁]; exact Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) fun w => i1 _
  have hZ₁ : ∫ y, j₁ y ≠ 0 := by
    rw [e₁, integral_fintype_prod_volume_eq_prod (fun w (z : ℂ) => ((‖z‖ ^ (κ w + 2 * e) * Real.exp (-2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ))]
    refine Finset.prod_ne_zero_iff.2 fun w _ => ?_
    rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
    refine (integral_pos_of_integrable_nonneg_nonzero (x := (1 : ℂ)) (by fun_prop) ?_ (fun z => by positivity) (by simp)).ne'
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using (i1 (κ w + 2 * e)).re
  have mg : Measurable (gm κ) := by unfold gm; fun_prop
  have mF : Measurable (FT (gm κ)) := (continuous_FT (integrable_gm κ)).measurable
  have mn : Measurable fun y : ι → ℂ => ((nm y : ℝ) : ℂ)⁻¹ := (Complex.continuous_ofReal.comp continuous_nm).measurable.inv
  have hj₂ : Integrable j₂ := by
    have e₂ : j₂ = fun y => ∏ w, (2⁻¹ * (-Complex.I) ^ κ w) * ((y w)⁻¹ ^ κ w * Complex.exp (-2 * Real.pi * (‖(y w)⁻¹‖ : ℂ) ^ 2)) *
        ((y w / (‖y w‖ : ℂ)) ^ κ w * (‖y w‖ : ℂ) ^ (2 * e)) * ((‖y w‖ : ℂ) ^ 2)⁻¹ := by
      funext y
      simp only [j₂, FT_gm, r0, nm, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Pi.inv_apply]
      push_cast; rfl
    rw [e₂]
    refine Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ)) (f := fun w z => (2⁻¹ * (-Complex.I) ^ κ w) *
      (z⁻¹ ^ κ w * Complex.exp (-2 * Real.pi * (‖z⁻¹‖ : ℂ) ^ 2)) * ((z / (‖z‖ : ℂ)) ^ κ w * (‖z‖ : ℂ) ^ (2 * e)) * ((‖z‖ : ℂ) ^ 2)⁻¹) fun w => ?_
    obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_lt (hκ w)
    refine int_of_le (by fun_prop) (Real.exp ((s + 3 : ℕ) ^ 2)) fun z hz => le_trans ?_ (poly_le ‖z‖⁻¹ (by positivity) (s + 3))
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hg := norm_gauss z⁻¹
    rw [norm_mul, norm_mul, norm_mul, norm_mul (z⁻¹ ^ κ w), hg]
    simp only [norm_mul, norm_pow, norm_inv, norm_neg, Complex.norm_I, one_pow, norm_div, Complex.norm_real, norm_norm,
      div_self hn.ne', mul_one, one_mul, Complex.norm_ofNat]
    have h2 : ‖z‖⁻¹ ^ s ≤ (1 + ‖z‖⁻¹) ^ s := pow_le_pow_left₀ (by positivity) (by linarith) s
    calc _ = 2⁻¹ * (‖z‖⁻¹ ^ s * (1 + ‖z‖⁻¹) ^ 3 * Real.exp (-2 * Real.pi * ‖z‖⁻¹ ^ 2)) := by
          rw [hs, pow_succ, pow_add, inv_pow _ (2 * e)]
          generalize ‖z‖⁻¹ ^ s = a
          have : ‖z‖ ^ (2 * e) ≠ 0 := by positivity
          generalize ‖z‖ ^ (2 * e) = b at *
          generalize Real.exp _ = c
          field_simp; ring
      _ ≤ 1 * ((1 + ‖z‖⁻¹) ^ s * (1 + ‖z‖⁻¹) ^ 3 * Real.exp (-2 * Real.pi * ‖z‖⁻¹ ^ 2)) := by gcongr; norm_num
      _ = _ := by ring
  refine ⟨(∫ y, j₂ y) / ∫ y, j₁ y, fun H hH hr hA => ?_⟩
  have k₁ := kernel (a := fun t => FT H t * (r0 κ e t)⁻¹) ((continuous_FT hH).measurable.mul (measurable_reduced_size κ e).inv).aestronglyMeasurable
    hj₁ (mg.mul (measurable_reduced_size κ e)) measurable_id (fun x hx => hx) (by simpa [mul_assoc] using hA)
  have hx' : ∀ᵐ x : ι → ℂ, H x * r0 κ e x = H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹) * ((nm x⁻¹ : ℝ) : ℂ)⁻¹ := by
    filter_upwards [ae_unit] with x hx
    have : ((nm x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
    rw [nm_inv]; push_cast; field_simp
  have k₂ := kernel (a := fun x => H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹)) (hH.1.mul ((measurable_reduced_size κ e).mul mn).aestronglyMeasurable)
    hj₂ (((mF.comp measurable_inv).mul (measurable_reduced_size κ e)).mul mn) measurable_inv (fun x hx w => inv_ne_zero (hx w)) (hr.congr hx')
  rw [← integral_congr_ae hx', integral_integral_swap k₂.1] at k₂
  rw [integral_integral_swap k₁.1] at k₁
  have key : ∫ y, ∫ t, FT H t * (r0 κ e t)⁻¹ * j₁ (id t * y) = ∫ y, ∫ x, H x * (r0 κ e x * ((nm x : ℝ) : ℂ)⁻¹) * j₂ (x⁻¹ * y) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_unit] with y hy
    have hny : ((nm y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hy).ne'
    calc _ = ∫ t, r0 κ e y * (FT H t * gm κ (y * t)) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_unit] with t ht
          have := rationalWeight_ne_zero κ e ht
          simp only [j₁, id, rationalWeight_mul, mul_comm t y]; field_simp
      _ = r0 κ e y * ∫ x, H x * FT (fun t => gm κ (y * t)) x := by
          rw [integral_const_mul, FT_mul hH (integrable_scale hy (integrable_gm κ))]
      _ = _ := by
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards [ae_unit] with x hx
          have hnx : ((nm x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nm_pos hx).ne'
          have h1 : r0 κ e x * r0 κ e x⁻¹ = 1 := by
            rw [← rationalWeight_mul, ← rationalWeight_one κ e]; congr 1; funext w; simp [hx w]
          have h2 : (x⁻¹ * y)⁻¹ = x * y⁻¹ := by funext w; simp [mul_comm]
          simp only [j₂, FT_scale (integrable_gm κ) hy, h2, rationalWeight_mul, nm_mul, nm_inv]
          push_cast
          generalize FT (gm κ) (x * y⁻¹) = A
          have h3 : ((nm x : ℝ) : ℂ)⁻¹ * ((nm x : ℝ) : ℂ) = 1 := inv_mul_cancel₀ hnx
          rw [mul_inv, inv_inv]
          linear_combination (-(H x * A * r0 κ e y * ((nm y : ℝ) : ℂ)⁻¹)) * (((nm x : ℝ) : ℂ)⁻¹ * ((nm x : ℝ) : ℂ) * h1 + h3)
  rw [k₁.2, k₂.2] at key
  simp only [id, mul_assoc] at key
  rw [div_mul_eq_mul_div, eq_div_iff hZ₁, key, mul_comm]

end PositivityTheory.ThKG.Loc.Bump

end
