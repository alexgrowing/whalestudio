import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCosSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StereographicMeasureChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusChangeOfVariables

set_option autoImplicit false

open MeasureTheory
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.LineCos.FsLaw

open GlobalTheory.LineCos

theorem re_det_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : 0 < G.det.re :=
  (Complex.pos_iff.1 hG.det_pos).1

theorem corner_eq {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) : G 0 0 = ((G 0 0).re : ℂ) := by
  have h := hG.isHermitian.apply 0 0
  exact (Complex.conj_eq_iff_re.1 h).symm

theorem hform_single (G : Matrix (Fin 2) (Fin 2) ℂ) (w : Fin 2 → ℂ) :
    hform G w (Pi.single 0 1) = w 0 * G 0 0 + w 1 * G 1 0 := by
  simp [hform, Fin.sum_univ_two]

theorem re_hform_mul {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (w : Fin 2 → ℂ) :
    (hform G w w).re * (G 0 0).re = ‖w 0 * G 0 0 + w 1 * G 1 0‖ ^ 2 + G.det.re * ‖w 1‖ ^ 2 := by
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.1 (hG.isHermitian.apply 1 1)
  have h01 : G 0 1 = starRingEnd ℂ (G 1 0) := (hG.isHermitian.apply 0 1).symm
  simp only [hform, Fin.sum_univ_two, Matrix.det_fin_two, h01, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.conj_re, Complex.conj_im,
    h00, h11]
  ring

theorem measurable_lineVec (s : Bool) (i : Fin 2) : Measurable fun x : ℂ => lineVec s x i := by
  cases s
  · fin_cases i
    · exact measurable_const
    · exact measurable_id
  · fin_cases i
    · exact measurable_id
    · exact measurable_const

theorem measurable_hform (G : Matrix (Fin 2) (Fin 2) ℂ) {a b : ℂ → Fin 2 → ℂ} (ha : ∀ i, Measurable fun x => a x i)
    (hb : ∀ i, Measurable fun x => b x i) : Measurable fun x => hform G (a x) (b x) := by
  unfold hform
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((ha i).mul (Complex.continuous_conj.measurable.comp (hb j))).mul_const _

theorem measurable_cosSq (s : Bool) (G : Matrix (Fin 2) (Fin 2) ℂ) : Measurable (cosSq s G) := by
  have h1 : Measurable fun x : ℂ => hform G (lineVec s x) (Pi.single (0 : Fin 2) (1 : ℂ)) :=
    measurable_hform G (b := fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) (measurable_lineVec s) fun _ => measurable_const
  have h2 : Measurable fun x : ℂ => (hform G (lineVec s x) (lineVec s x)).re :=
    Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
  exact (h1.norm.pow_const 2).div (h2.mul_const _)

theorem lintegral_reflect (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, g (1 - t) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_sub_left_eq_self ((Set.Ioo (0 : ℝ) 1).indicator g) 1]
  congr 1
  funext t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · have : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [Set.indicator_of_mem ht, Set.indicator_of_mem this]
  · have : 1 - t ∉ Set.Ioo (0 : ℝ) 1 := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem this]

theorem lintegral_false {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec false x) (lineVec false x)).re ^ 2)) *
      g (cosSq false G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((Real.sqrt D / a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos (Real.sqrt_pos.2 hD) ha).ne'
  have hH : Measurable fun x : ℂ =>
      g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← GlobalTheory.FibLine.lintegral_comp_fsDens g hg,
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius (G 1 0 / a) _ hc _ hH]
  refine lintegral_congr_ae ?_
  filter_upwards [GlobalTheory.FibLine.UnitaryInv.ae_affine_ne 1 (G 1 0 / a) (Or.inl one_ne_zero)] with x hx
  have hsq := re_hform_mul hG (lineVec false x)
  have hone := hform_single G (lineVec false x)
  have hw0 : lineVec false x 0 = 1 := rfl
  have hw1 : lineVec false x 1 = x := rfl
  have hp : 1 * G 0 0 + x * G 1 0 = a * (1 + G 1 0 / a * x) := by
    rw [hG0]; field_simp
  rw [hw0, hw1, hp] at hsq hone
  set q : ℝ := ‖1 + G 1 0 / a * x‖ with hq_def
  have hq : 0 < q := norm_pos_iff.2 hx
  have hn : ‖(a : ℂ) * (1 + G 1 0 / a * x)‖ = a * q := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((Real.sqrt D / a : ℝ) : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((Real.sqrt D / a : ℝ) : ℂ) * x / (1 + G 1 0 / a * x)‖ ^ 2 = D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2 := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hcn]
  have hj : ‖((Real.sqrt D / a : ℝ) : ℂ) / (1 + G 1 0 / a * x) ^ 2‖ ^ 2 = D / a ^ 2 / q ^ 4 := by
    rw [norm_div, norm_pow, div_pow, hcn, ← pow_mul]
  rw [hn, ← ha_def, ← hD_def] at hsq
  have hh : (hform G (lineVec false x) (lineVec false x)).re = ((a * q) ^ 2 + D * ‖x‖ ^ 2) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq false G x = 1 / (1 + D / a ^ 2 * ‖x‖ ^ 2 / q ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

theorem lintegral_true {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x : ℂ, ENNReal.ofReal (G.det.re / (Real.pi * (hform G (lineVec true x) (lineVec true x)).re ^ 2)) *
      g (cosSq true G x) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have ha : 0 < a := re_corner_pos hG
  have hD : 0 < D := re_det_pos hG
  have hG0 : G 0 0 = (a : ℂ) := corner_eq hG
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hc : ((a / Real.sqrt D : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (div_pos ha (Real.sqrt_pos.2 hD)).ne'
  have hg' : Measurable fun t : ℝ => g (1 - t) := hg.comp (by fun_prop)
  have hH : Measurable fun x : ℂ =>
      g (1 - 1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) := by
    have : Measurable fun x : ℂ => g (1 - 1 / (1 + ‖x‖ ^ 2)) := hg.comp (by fun_prop)
    fun_prop
  rw [← lintegral_reflect, ← GlobalTheory.FibLine.lintegral_comp_fsDens _ hg',
    ← GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius 0 _ hc _ hH,
    ← lintegral_sub_right_eq_self _ (G 1 0 / a)]
  refine lintegral_congr fun x => ?_
  have hsq := re_hform_mul hG (lineVec true (x - G 1 0 / a))
  have hone := hform_single G (lineVec true (x - G 1 0 / a))
  have hw0 : lineVec true (x - G 1 0 / a) 0 = x - G 1 0 / a := rfl
  have hw1 : lineVec true (x - G 1 0 / a) 1 = 1 := rfl
  have hp : (x - G 1 0 / a) * G 0 0 + 1 * G 1 0 = a * x := by
    rw [hG0]; field_simp; ring
  rw [hw0, hw1, hp] at hsq hone
  have hn : ‖(a : ℂ) * x‖ = a * ‖x‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have hcn : ‖((a / Real.sqrt D : ℝ) : ℂ)‖ ^ 2 = a ^ 2 / D := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hD.le]
  have hy : ‖((a / Real.sqrt D : ℝ) : ℂ) * x / (1 + 0 * x)‖ ^ 2 = a ^ 2 / D * ‖x‖ ^ 2 := by
    rw [zero_mul, add_zero, div_one, norm_mul, mul_pow, hcn]
  have hj : ‖((a / Real.sqrt D : ℝ) : ℂ) / (1 + 0 * x) ^ 2‖ ^ 2 = a ^ 2 / D := by
    rw [zero_mul, add_zero, one_pow, div_one, hcn]
  rw [hn, ← ha_def, ← hD_def, norm_one, one_pow, mul_one] at hsq
  have hh : (hform G (lineVec true (x - G 1 0 / a)) (lineVec true (x - G 1 0 / a))).re = ((a * ‖x‖) ^ 2 + D) / a :=
    eq_div_of_mul_eq ha.ne' hsq
  have hcos : cosSq true G (x - G 1 0 / a) = 1 - 1 / (1 + a ^ 2 / D * ‖x‖ ^ 2) := by
    unfold cosSq
    rw [hone, hn, ← ha_def, hsq]
    field_simp
    ring
  have hpi := Real.pi_pos
  rw [hy, hj, hcos, hh, mul_left_comm, mul_comm, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
  ring

theorem map_cosSq_fs (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (hG : G.PosDef) :
    Measure.map (cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hd : Measurable fun x : ℂ => ENNReal.ofReal (G.det.re /
      (Real.pi * (hform G (lineVec s x) (lineVec s x)).re ^ 2)) := by
    have := Complex.measurable_re.comp (measurable_hform G (measurable_lineVec s) (measurable_lineVec s))
    exact (measurable_const.div ((this.pow_const 2).const_mul _)).ennreal_ofReal
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg (measurable_cosSq s G),
    lintegral_withDensity_eq_lintegral_mul _ hd (g := fun x => g (cosSq s G x)) (hg.comp (measurable_cosSq s G)),
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  cases s
  · exact lintegral_false hG g hg
  · exact lintegral_true hG g hg

end GlobalTheory.LineCos.FsLaw
