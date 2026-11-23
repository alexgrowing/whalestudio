import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Perron
import Formalism.ZetaNonvanishing.MellinSgen

open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

def vonMangoldtCharRe (n : ℕ) : ℝ := (Λ n : ℝ) * (χ (n : ZMod q)).re

def vonMangoldtCharIm (n : ℕ) : ℝ := (Λ n : ℝ) * (χ (n : ZMod q)).im

lemma vonMangoldtCharRe_bound (n : ℕ) : |vonMangoldtCharRe χ n| ≤ 1 * Λ n := by
  unfold vonMangoldtCharRe
  have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_mul, abs_of_nonneg hΛ, one_mul]
  refine mul_le_of_le_one_right hΛ ?_
  refine le_trans ?_ (DirichletCharacter.norm_le_one χ (n : ZMod q))
  first
  | exact Complex.abs_re_le_norm _
  | exact Complex.abs_re_le_abs _

lemma vonMangoldtCharIm_bound (n : ℕ) : |vonMangoldtCharIm χ n| ≤ 1 * Λ n := by
  unfold vonMangoldtCharIm
  have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_mul, abs_of_nonneg hΛ, one_mul]
  refine mul_le_of_le_one_right hΛ ?_
  refine le_trans ?_ (DirichletCharacter.norm_le_one χ (n : ZMod q))
  first
  | exact Complex.abs_im_le_norm _
  | exact Complex.abs_im_le_abs _

lemma vonMangoldtCharRe_zero : vonMangoldtCharRe χ 0 = 0 := by simp [vonMangoldtCharRe]

lemma vonMangoldtCharIm_zero : vonMangoldtCharIm χ 0 = 0 := by simp [vonMangoldtCharIm]

lemma chebyshev_character_re_im (x : ℝ) :
    Schi χ x = (Formalism.Sa (vonMangoldtCharRe χ) x : ℂ) + I * (Formalism.Sa (vonMangoldtCharIm χ) x : ℂ) := by
  unfold Schi Formalism.Sa vonMangoldtCharRe vonMangoldtCharIm
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => rw [← Complex.re_add_im (χ (n : ZMod q))]
  ring

lemma chebyshev_character_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : Schi χ x = 0 := by
  unfold Schi
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_Icc] at hn
  have h1 : ⌊x⌋₊ ≤ 1 := (Nat.floor_mono hx).trans_eq Nat.floor_one
  have hn1 : n = 1 := by omega
  subst hn1
  simp

end

section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

lemma lseries_summable_of_vonMangoldt_bound {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => (a n : ℂ)) w := by
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hw
  have hb : ∀ n, ‖LSeries.term (fun n => (a n : ℂ)) w n‖ ≤ ‖LSeries.term (fun n => (Λ n : ℂ)) w n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · exact le_rfl
    · gcongr
      have h2 := ha n
      have h3 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      simpa [Complex.norm_real, abs_of_nonneg h3] using h2
  first
  | exact Summable.of_norm_bounded hΛ.norm hb
  | exact Summable.of_norm_bounded _ hΛ.norm hb

lemma neg_log_deriv_eq_lseries_mul_vonMangoldt {w : ℂ} (hw : 1 < w.re) : negLD χ w = LSeries (↗χ * ↗Λ) w := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hw, neg_div]
  have hEq : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s = L (fun n => χ n) s :=
    fun s hs => DirichletCharacter.LFunction_eq_LSeries χ hs
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 w] L (fun n => χ n) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with s hs
    exact hEq s hs
  rw [hev.deriv_eq, hEq w hw]

lemma neg_log_deriv_eq_lseries_re_im {w : ℂ} (hw : 1 < w.re) :
    negLD χ w = LSeries (fun n => (vonMangoldtCharRe χ n : ℂ)) w +
      I * LSeries (fun n => (vonMangoldtCharIm χ n : ℂ)) w := by
  have h1 := lseries_summable_of_vonMangoldt_bound (vonMangoldtCharRe_bound χ) hw
  have h2 := lseries_summable_of_vonMangoldt_bound (vonMangoldtCharIm_bound χ) hw
  rw [neg_log_deriv_eq_lseries_mul_vonMangoldt χ hw, ← LSeries_smul, ← LSeries_add h1 (h2.smul I)]
  congr 1
  funext n
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, vonMangoldtCharRe, vonMangoldtCharIm]
  push_cast
  conv_lhs => rw [← Complex.re_add_im (χ (n : ZMod q))]
  ring

lemma norm_neg_log_deriv_le_tsum {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖negLD χ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
  have hw' : 1 < w.re := by rw [hw]; exact hσ
  rw [neg_log_deriv_eq_lseries_mul_vonMangoldt χ hw']
  have hs : LSeriesSummable (fun n => (Λ n : ℂ)) (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hb : ∀ n, ‖LSeries.term (↗χ * ↗Λ) w n‖ ≤ ‖LSeries.term (fun n => (Λ n : ℂ)) (σ₀ : ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs
    · exact le_rfl
    · rw [hw, Complex.ofReal_re]
      gcongr
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hsum : Summable fun n => ‖LSeries.term (↗χ * ↗Λ) w n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs.norm
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  first
  | exact tsum_le_tsum hb hsum hs.norm
  | exact Summable.tsum_le_tsum hb hsum hs.norm

lemma perron_integrand_continuous {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 < s.re} := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl (by rintro rfl; simp at hs))).differentiableWithinAt
  have hdz : ContinuousOn (deriv (DirichletCharacter.LFunction χ)) {s : ℂ | 1 < s.re} :=
    (hz.deriv hU).continuousOn
  have hline : Continuous (fun t : ℝ => (σ₀ : ℂ) + t * I) := by fun_prop
  have hmem : ∀ t : ℝ, (σ₀ : ℂ) + t * I ∈ {s : ℂ | 1 < s.re} := by intro t; simp [hσ]
  have c1 : Continuous (fun t : ℝ => deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + t * I)) :=
    hdz.comp_continuous hline hmem
  have c2 : Continuous (fun t : ℝ => DirichletCharacter.LFunction χ ((σ₀ : ℂ) + t * I)) :=
    hz.continuousOn.comp_continuous hline hmem
  have hne : ∀ t : ℝ, DirichletCharacter.LFunction χ ((σ₀ : ℂ) + t * I) ≠ 0 := fun t => by
    have h1 : 1 < ((σ₀ : ℂ) + t * I).re := by simp [hσ]
    rw [DirichletCharacter.LFunction_eq_LSeries χ h1]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ h1
  have c3 : Continuous (fun t : ℝ => (y : ℂ) ^ ((σ₀ : ℂ) + t * I)) :=
    hline.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  have hw0 : ∀ t : ℝ, ((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1) ≠ 0 := by
    intro t
    apply mul_ne_zero
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold Fchi negLD
  exact ((c1.div c2 hne).neg.mul c3).div (hline.mul (hline.sub continuous_const)) hw0

lemma perron_integrand_integrable {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Integrable (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) := by
  set B := ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ with hBdef
  have hB : 0 ≤ B := tsum_nonneg (fun n => norm_nonneg _)
  set dd := min ((σ₀ - 1) ^ 2) 1 with hdddef
  have hdd : 0 < dd := lt_min (by nlinarith) one_pos
  have hy' : 0 < y ^ σ₀ := Real.rpow_pos_of_pos hy _
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (B * y ^ σ₀ / dd))
    (perron_integrand_continuous χ hy hσ).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hre : ((σ₀ : ℂ) + t * I).re = σ₀ := by simp
  unfold Fchi
  rw [norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy, hre]
  have hL := norm_neg_log_deriv_le_tsum χ hσ _ hre
  have hD := Formalism.ZF.perron_denom_bound hσ t
  have hpos : 0 < dd * (1 + t ^ 2) := by positivity
  have hc : 0 ≤ B * y ^ σ₀ / dd * (1 + t ^ 2)⁻¹ :=
    mul_nonneg (div_nonneg (mul_nonneg hB hy'.le) hdd.le) (inv_nonneg.mpr (by positivity))
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hD)]
  calc ‖negLD χ ((σ₀ : ℂ) + t * I)‖ * y ^ σ₀ ≤ B * y ^ σ₀ :=
        mul_le_mul_of_nonneg_right hL hy'.le
    _ = B * y ^ σ₀ / dd * (1 + t ^ 2)⁻¹ * (dd * (1 + t ^ 2)) := by
        field_simp
    _ ≤ B * y ^ σ₀ / dd * (1 + t ^ 2)⁻¹ * ‖((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1)‖ :=
        mul_le_mul_of_nonneg_left hD hc

end

section
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

lemma summatory_eq_sum_range {a : ℕ → ℝ} (ha0 : a 0 = 0) {N : ℕ} {x : ℝ} (hx : x < N) :
    Formalism.Sa a x = ∑ n ∈ Finset.range N, a n * Formalism.mxS n x := by
  rw [Formalism.Sa_eq_tsum _ ha0]
  refine tsum_eq_sum (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have hxn : x < n := lt_of_lt_of_le hx (by exact_mod_cast hn)
  refine Formalism.a_mxS_eq_zero _ ha0 x n ?_
  rw [Finset.mem_Icc]
  rintro ⟨h1, h2⟩
  have hx1 : 1 ≤ x := Nat.floor_pos.mp (by omega)
  have : (n : ℝ) ≤ x := (Nat.cast_le.mpr h2).trans (Nat.floor_le (by linarith))
  linarith

lemma summatory_function_continuousAt {a : ℕ → ℝ} (ha0 : a 0 = 0) (y : ℝ) :
    ContinuousAt (fun x => (Formalism.Sa a x : ℂ)) y := by
  obtain ⟨N, hN⟩ := exists_nat_gt y
  have hev : (fun x => ((∑ n ∈ Finset.range N, a n * Formalism.mxS n x : ℝ) : ℂ)) =ᶠ[𝓝 y]
      (fun x => (Formalism.Sa a x : ℂ)) := by
    filter_upwards [eventually_lt_nhds hN] with x hx
    rw [summatory_eq_sum_range ha0 hx]
  refine ContinuousAt.congr ?_ hev
  exact (Complex.continuous_ofReal.comp (continuous_finsetSum _
    (fun n _ => continuous_const.mul (Formalism.ZF.perron_continuous_mxS n)))).continuousAt

lemma chebyshev_character_continuousAt (y : ℝ) : ContinuousAt (fun x => Schi χ x) y := by
  have h : (fun x => Schi χ x) =
      fun x => (Formalism.Sa (vonMangoldtCharRe χ) x : ℂ) + I * (Formalism.Sa (vonMangoldtCharIm χ) x : ℂ) :=
    funext (chebyshev_character_re_im χ)
  rw [h]
  exact (summatory_function_continuousAt (vonMangoldtCharRe_zero χ) y).add
    (continuousAt_const.mul (summatory_function_continuousAt (vonMangoldtCharIm_zero χ) y))

lemma summatory_rpow_integrableOn {a : ℕ → ℝ} (ha : ∀ n, |a n| ≤ 1 * Λ n) {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (Formalism.Sa a x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) := by
  obtain ⟨hm, hI, -⟩ := Formalism.mellinSgen a 1 ha
  refine Integrable.mono' (hI w.re hw) ?_ ?_
  · exact ((Complex.measurable_ofReal.comp hm).mul
      (Complex.measurable_ofReal.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
    simp

lemma chebyshev_character_integrableOn {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w - 1) • Schi χ x) (Ioi 1) := by
  refine ((summatory_rpow_integrableOn (vonMangoldtCharRe_bound χ) hw).add
    ((summatory_rpow_integrableOn (vonMangoldtCharIm_bound χ) hw).const_mul I)).congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [Pi.add_apply, chebyshev_character_re_im χ x, smul_eq_mul]
  ring

lemma mellin_chebyshev_character {w : ℂ} (hw : 1 < w.re) :
    mellin (fun x : ℝ => Schi χ x) (-w) = negLD χ w / (w * (w - 1)) := by
  have h1 := (Formalism.mellinSgen _ 1 (vonMangoldtCharRe_bound χ)).2.2 w hw
  have h2 := (Formalism.mellinSgen _ 1 (vonMangoldtCharIm_bound χ)).2.2 w hw
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) ?_]
  · calc ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-w - 1) • Schi χ t
        = ∫ t in Ioi (1:ℝ), ((Formalism.Sa (vonMangoldtCharRe χ) t : ℂ) * (t : ℂ) ^ (-w - 1) +
            I * ((Formalism.Sa (vonMangoldtCharIm χ) t : ℂ) * (t : ℂ) ^ (-w - 1))) := by
          congr 1; funext t; rw [chebyshev_character_re_im χ t, smul_eq_mul]; ring
      _ = (∫ t in Ioi (1:ℝ), (Formalism.Sa (vonMangoldtCharRe χ) t : ℂ) * (t : ℂ) ^ (-w - 1)) +
            I * ∫ t in Ioi (1:ℝ), (Formalism.Sa (vonMangoldtCharIm χ) t : ℂ) * (t : ℂ) ^ (-w - 1) := by
          rw [integral_add (summatory_rpow_integrableOn (vonMangoldtCharRe_bound χ) hw)
            ((summatory_rpow_integrableOn (vonMangoldtCharIm_bound χ) hw).const_mul I), integral_const_mul]
      _ = _ := by
          rw [h1, h2, neg_log_deriv_eq_lseries_re_im χ hw]
          ring
  · intro x hx
    have hx1 : x ≤ 1 := not_lt.mp hx.2
    simp [chebyshev_character_eq_zero_of_le_one χ hx1]

lemma mellin_convergent_chebyshev_character {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => Schi χ x) ((-σ₀ : ℝ) : ℂ) := by
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_zero).congr_fun (fun x hx => ?_) measurableSet_Ioc
    simp [chebyshev_character_eq_zero_of_le_one χ hx.2]
  · have h := chebyshev_character_integrableOn χ (w := (σ₀ : ℂ)) (by simpa using hσ)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [ofReal_neg]

lemma perron_vertical_integrable {σ₀ : ℝ} (hσ : 1 < σ₀) :
    VerticalIntegrable (mellin (fun x : ℝ => Schi χ x)) (-σ₀) := by
  show Integrable (fun t : ℝ => mellin (fun x : ℝ => Schi χ x) (((-σ₀ : ℝ) : ℂ) + t * I))
  have h1 := (perron_integrand_integrable χ one_pos hσ).comp_neg
  refine h1.congr (Eventually.of_forall fun t => ?_)
  show Fchi χ 1 ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) =
    mellin (fun x : ℝ => Schi χ x) (((-σ₀ : ℝ) : ℂ) + t * I)
  have hw : ((-σ₀ : ℝ) : ℂ) + t * I = -((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) := by push_cast; ring
  rw [hw, mellin_chebyshev_character χ (by simp [hσ])]
  unfold Fchi
  rw [ofReal_one, one_cpow, mul_one]

end

theorem perron_formula_character : PerronChi := by
  intro q _ χ y hy σ₀ hσ
  have hy0 : 0 < y := by linarith
  refine ⟨perron_integrand_integrable χ hy0 hσ, ?_⟩
  have hinv := mellinInv_mellin_eq (-σ₀) (fun x : ℝ => Schi χ x) hy0
    (mellin_convergent_chebyshev_character χ hσ) (perron_vertical_integrable χ hσ) (chebyshev_character_continuousAt χ y)
  rw [← hinv]
  unfold mellinInv
  have key : ∀ t : ℝ, (y : ℂ) ^ (-(((-σ₀ : ℝ) : ℂ) + t * I)) •
      mellin (fun x : ℝ => Schi χ x) (((-σ₀ : ℝ) : ℂ) + t * I) =
      Fchi χ y ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    intro t
    have hw : ((-σ₀ : ℝ) : ℂ) + t * I = -((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) := by push_cast; ring
    rw [hw, mellin_chebyshev_character χ (by simp [hσ]), neg_neg, smul_eq_mul]
    unfold Fchi
    ring
  rw [integral_congr_ae (Eventually.of_forall key)]
  have h2 : ∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) =
      ∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + (t : ℂ) * I) :=
    integral_neg_eq_self (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + (t : ℂ) * I)) volume
  rw [h2, Complex.real_smul]
  push_cast
  ring

end Formalism.ZeroFreeDirichlet
