import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFS
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem gaM_hasDerivAt_antider {b : ℝ} (hb : 0 < b) (j : ℕ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(1 / (2 * ((j : ℝ) + 1))) * ((b + r ^ 2) ^ (j + 1))⁻¹)
      (r * ((b + r ^ 2) ^ (j + 2))⁻¹) r := by
  have hpos : 0 < b + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => b + r ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add b
  have h2 := (h1.pow (j + 1)).inv (pow_ne_zero _ hpos.ne')
  have h3 := h2.const_mul (-(1 / (2 * ((j : ℝ) + 1))))
  simp only [Nat.add_sub_cancel] at h3
  have h4 : HasDerivAt (fun r : ℝ => -(1 / (2 * ((j : ℝ) + 1))) * ((b + r ^ 2) ^ (j + 1))⁻¹)
      (-(1 / (2 * ((j : ℝ) + 1))) * (-(((j + 1 : ℕ) : ℝ) * (b + r ^ 2) ^ j * (2 * r)) /
        ((b + r ^ 2) ^ (j + 1)) ^ 2)) r := h3
  refine h4.congr_deriv ?_
  have hj : (2 * ((j : ℝ) + 1)) ≠ 0 := by positivity
  have hX : (b + r ^ 2) ≠ 0 := hpos.ne'
  field_simp
  push_cast
  ring

theorem gaM_tendsto_antider {b : ℝ} (_hb : 0 < b) (j : ℕ) :
    Tendsto (fun r : ℝ => -(1 / (2 * ((j : ℝ) + 1))) * ((b + r ^ 2) ^ (j + 1))⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => b + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (b + r ^ 2) ^ (j + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero j)).comp h1
  simpa using (tendsto_inv_atTop_zero.comp h2).const_mul (-(1 / (2 * ((j : ℝ) + 1))))

theorem gaM_integrableOn_Ioi {b : ℝ} (hb : 0 < b) (j : ℕ) :
    IntegrableOn (fun r : ℝ => r * ((b + r ^ 2) ^ (j + 2))⁻¹) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => gaM_hasDerivAt_antider hb j x)
    (fun x hx => by have : 0 < b + x ^ 2 := by positivity
                    exact mul_nonneg (le_of_lt hx) (by positivity))
    (gaM_tendsto_antider hb j)

theorem gaM_integral_Ioi {b : ℝ} (hb : 0 < b) (j : ℕ) :
    ∫ r in Ioi (0 : ℝ), r * ((b + r ^ 2) ^ (j + 2))⁻¹ = 1 / (2 * ((j : ℝ) + 1) * b ^ (j + 1)) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => gaM_hasDerivAt_antider hb j x)
    (fun x hx => by have : 0 < b + x ^ 2 := by positivity
                    exact mul_nonneg (le_of_lt hx) (by positivity))
    (gaM_tendsto_antider hb j)]
  have : (0 : ℝ) < b ^ (j + 1) := by positivity
  field_simp
  ring

theorem gaM_lintegral_complex {b : ℝ} (hb : 0 < b) (j : ℕ) :
    ∫⁻ t : ℂ, ENNReal.ofReal (((b + ‖t‖ ^ 2) ^ (j + 2))⁻¹) =
      ENNReal.ofReal (Real.pi / (((j : ℝ) + 1) * b ^ (j + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hcongr : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      ENNReal.ofReal (((b + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (j + 2))⁻¹) =
      ENNReal.ofReal (p.1 * ((b + p.1 ^ 2) ^ (j + 2))⁻¹) * 1 := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1, smul_eq_mul, mul_one,
      ENNReal.ofReal_mul hp1.le]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((b + r ^ 2) ^ (j + 2))⁻¹))
    (g := fun _ : ℝ => (1 : ℝ≥0∞)) (by fun_prop) aemeasurable_const]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaM_integrableOn_Ioi hb j)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
      have : 0 < b + x ^ 2 := by positivity
      exact mul_nonneg (le_of_lt hx) (by positivity))]
  rw [gaM_integral_Ioi hb j, setLIntegral_one, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : (0 : ℝ) < b ^ (j + 1) := by positivity
  field_simp
  ring

theorem gaM_lintegral_pi (D : ℕ) : ∀ (a : ℝ), 0 < a → ∀ j : ℕ,
    ∫⁻ y : Fin D → ℂ, ENNReal.ofReal (((a + ∑ i, ‖y i‖ ^ 2) ^ (D + j + 1))⁻¹) =
      ENNReal.ofReal (Real.pi ^ D * (j.factorial : ℝ) / (((D + j).factorial : ℝ) * a ^ (j + 1))) := by
  induction D with
  | zero =>
    intro a ha j
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add, pow_zero, one_mul]
    rw [lintegral_const, MeasureTheory.volume_pi, Measure.pi_univ, Finset.univ_eq_empty,
      Finset.prod_empty, mul_one]
    congr 1
    have : (0 : ℝ) < (j.factorial : ℝ) := by positivity
    field_simp
  | succ D ih =>
    intro a ha j
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0
    set F : (Fin (D + 1) → ℂ) → ℝ≥0∞ := fun y =>
      ENNReal.ofReal (((a + ∑ i, ‖y i‖ ^ 2) ^ (D + 1 + j + 1))⁻¹) with hF
    have hFm : Measurable F := by
      have : Continuous fun y : Fin (D + 1) → ℂ => ((a + ∑ i, ‖y i‖ ^ 2) ^ (D + 1 + j + 1))⁻¹ := by
        refine Continuous.inv₀ (by fun_prop) fun y => ?_
        have : 0 < a + ∑ i, ‖y i‖ ^ 2 := by positivity
        positivity
      exact ENNReal.measurable_ofReal.comp this.measurable
    have h1 := hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
      (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0).symm p))
    simp only [MeasurableEquiv.symm_apply_apply] at h1
    rw [h1, Measure.volume_eq_prod,
      lintegral_prod (fun p => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0).symm p))
        ((hFm.comp (MeasurableEquiv.measurable _)).aemeasurable)]
    have h2 : ∀ t : ℂ, ∫⁻ y', F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0).symm (t, y')) =
        ENNReal.ofReal (Real.pi ^ D * ((j + 1).factorial : ℝ) / (((D + (j + 1)).factorial : ℝ))) *
          ENNReal.ofReal (((a + ‖t‖ ^ 2) ^ (j + 2))⁻¹) := by
      intro t
      have ht : 0 < a + ‖t‖ ^ 2 := by positivity
      have := ih (a + ‖t‖ ^ 2) ht (j + 1)
      have hexp : D + (j + 1) + 1 = D + 1 + j + 1 := by ring
      rw [hexp] at this
      simp only [hF, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_zero', Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← add_assoc]
      rw [this, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : 0 < (a + ‖t‖ ^ 2) ^ (j + 2) := by positivity
      field_simp
      rw [show D + j + 1 = D + (j + 1) by ring]
    simp_rw [h2]
    rw [lintegral_const_mul _ (by fun_prop), gaM_lintegral_complex ha j, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hfj : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by push_cast [Nat.factorial_succ]; ring
    have hfD : ((D + 1 + j).factorial : ℝ) = ((D + (j + 1)).factorial : ℝ) := by
      rw [show D + 1 + j = D + (j + 1) by ring]
    rw [hfj, hfD]
    have : (0 : ℝ) < ((D + (j + 1)).factorial : ℝ) := by positivity
    have : (0 : ℝ) < a ^ (j + 1) := by positivity
    field_simp
    ring

theorem gaM_integral_fsDens (D : ℕ) :
    ∫ y : Fin D → ℂ, ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹ = Real.pi ^ D / (D.factorial : ℝ) := by
  have hnn : ∀ y : Fin D → ℂ, 0 ≤ ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹ := fun y => by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
    (Continuous.aestronglyMeasurable (by
      refine Continuous.inv₀ (by fun_prop) fun y => ?_
      have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
      positivity))]
  have := gaM_lintegral_pi D 1 one_pos 0
  simp only [add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_pow] at this
  rw [this, ENNReal.toReal_ofReal (by positivity)]

section FS

open ReciprocityTheory.ChartRestriction.G.Geo

variable {D : ℕ}

def gbBilL (D : ℕ) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v u => ∑ i, ((v i).re * (u i).re + (v i).im * (u i).im))
    (fun a b c => by simp only [Pi.add_apply, Complex.add_re, Complex.add_im, ← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun r a b => by simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)
    (fun a b c => by simp only [Pi.add_apply, Complex.add_re, Complex.add_im, ← Finset.sum_add_distrib]; congr 1; ext; ring)
    (fun r a b => by simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul, Finset.mul_sum]; congr 1; ext; ring)

def gbBil (D : ℕ) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin D → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ gbBilL D)

theorem gbBil_apply (v u : Fin D → ℂ) :
    gbBil D v u = ∑ i, ((v i).re * (u i).re + (v i).im * (u i).im) := rfl

theorem gbBil_comm (v u : Fin D → ℂ) : gbBil D v u = gbBil D u v := by
  simp only [gbBil_apply]; congr 1; ext; ring

def gbG (y : Fin D → ℂ) : ℝ := 1 + ∑ i, ‖y i‖ ^ 2

def gbPot (y : Fin D → ℂ) : ℝ := Real.log (Real.sqrt (1 + ∑ i, ‖y i‖ ^ 2))

theorem gbG_pos (y : Fin D → ℂ) : 0 < gbG y := by unfold gbG; positivity

theorem gbG_eq (y : Fin D → ℂ) : gbG y = 1 + gbBil D y y := by
  rw [gbG, gbBil_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

theorem hasFDerivAt_gbG (y : Fin D → ℂ) : HasFDerivAt gbG (2 • gbBil D y) y := by
  have h := (gbBil D).hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
  have h2 := h.const_add 1
  have hfun : (fun y' => 1 + gbBil D (id y') (id y')) = gbG := funext fun y' => (gbG_eq y').symm
  rw [hfun] at h2
  refine h2.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  simp
  rw [gbBil_comm u y]
  ring

theorem gbPot_eq (y : Fin D → ℂ) : gbPot y = Real.log (gbG y) / 2 := by
  show Real.log (Real.sqrt (gbG y)) = _
  rw [Real.log_sqrt (gbG_pos y).le]

theorem hasFDerivAt_gbPot (y : Fin D → ℂ) : HasFDerivAt gbPot ((gbG y)⁻¹ • gbBil D y) y := by
  have h := HasFDerivAt.const_mul (HasFDerivAt.log (hasFDerivAt_gbG y) (gbG_pos y).ne') (1 / 2 : ℝ)
  have hfun : (fun y' : Fin D → ℂ => (1 / 2 : ℝ) * Real.log (gbG y')) = gbPot :=
    funext fun y' => by rw [gbPot_eq]; ring
  rw [hfun] at h
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun u => ?_
  simp
  ring

theorem fderiv_gbPot : fderiv ℝ gbPot = fun y : Fin D → ℂ => (gbG y)⁻¹ • gbBil D y :=
  funext fun y => (hasFDerivAt_gbPot y).fderiv

theorem hasFDerivAt_fderiv_gbPot (y : Fin D → ℂ) :
    HasFDerivAt (fderiv ℝ gbPot)
      ((gbG y)⁻¹ • gbBil D + ((-((gbG y) ^ 2)⁻¹) • (2 • gbBil D y)).smulRight (gbBil D y)) y := by
  rw [fderiv_gbPot]
  have hi : HasFDerivAt (fun y => (gbG y)⁻¹) ((-((gbG y) ^ 2)⁻¹) • (2 • gbBil D y)) y := by
    have := (hasDerivAt_inv (gbG_pos y).ne').comp_hasFDerivAt y (hasFDerivAt_gbG y)
    exact this
  exact hi.smul (gbBil D).hasFDerivAt

theorem fderiv_fderiv_gbPot_apply (y v u : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ gbPot) y v u =
      (gbG y)⁻¹ * gbBil D v u - 2 * ((gbG y) ^ 2)⁻¹ * gbBil D y v * gbBil D y u := by
  rw [(hasFDerivAt_fderiv_gbPot y).fderiv]
  simp
  ring

theorem gbBil_single (y : Fin D → ℂ) (i : Fin D) (a : ℂ) :
    gbBil D y (Pi.single i a) = (y i).re * a.re + (y i).im * a.im := by
  rw [gbBil_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Pi.single_apply, hk]
  · simp

theorem gb_I_single (i : Fin D) : (Complex.I • Pi.single i (1 : ℂ) : Fin D → ℂ) = Pi.single i Complex.I := by
  ext k; by_cases h : k = i
  · subst h; simp
  · simp [h, Pi.single_apply]

theorem gb_conj_mul (u v : ℂ) : starRingEnd ℂ u * v =
    ((u.re * v.re + u.im * v.im : ℝ) : ℂ) + ((u.re * v.im - u.im * v.re : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp <;> ring

theorem cxHessian_gbPot (y : Fin D → ℂ) (i j : Fin D) :
    cxHessian gbPot y i j =
      (((gbG y : ℂ) * (if i = j then 1 else 0) - starRingEnd ℂ (y i) * y j) / (2 * (gbG y : ℂ) ^ 2)) := by
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  simp only [cxHessian, fderiv_fderiv_gbPot_apply, gb_I_single, gbBil_single, gb_conj_mul]
  by_cases h : i = j
  · subst h
    simp only [Pi.single_apply, if_true, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    field_simp
    ring
  · simp only [Pi.single_apply, h, Ne.symm h, if_false, Complex.zero_re, Complex.zero_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
    push_cast
    field_simp
    ring

theorem cxHessian_gbPot_eq (y : Fin D → ℂ) :
    cxHessian gbPot y = (1 / (2 * (gbG y : ℂ))) •
      (1 + Matrix.replicateCol Unit (fun i => -(starRingEnd ℂ (y i)) / (gbG y : ℂ)) *
        Matrix.replicateRow Unit y) := by
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  ext i j
  rw [cxHessian_gbPot]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply, smul_eq_mul]
  field_simp
  ring

theorem det_cxHessian_gbPot (y : Fin D → ℂ) :
    (cxHessian gbPot y).det = 1 / ((2 : ℂ) ^ D * (gbG y : ℂ) ^ (D + 1)) := by
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  rw [cxHessian_gbPot_eq, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : ∑ i, y i * starRingEnd ℂ (y i) = ((gbG y - 1 : ℝ) : ℂ) := by
    rw [gbG, add_sub_cancel_left, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdot : y ⬝ᵥ (fun i => -(starRingEnd ℂ (y i)) / (gbG y : ℂ)) =
      -(∑ i, y i * starRingEnd ℂ (y i)) / (gbG y : ℂ) := by
    simp only [dotProduct, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdot, hs, Fintype.card_fin]
  push_cast
  simp only [inv_pow, one_div_pow, one_div]
  field_simp
  ring

theorem maDensity_gbPot (y : Fin D → ℂ) :
    maDensity (fun _ : Fin D => gbPot) y =
      (D.factorial : ℝ) / Real.pi ^ D * ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹ := by
  have hmd : mixedDisc (fun _ : Fin D => cxHessian gbPot y) = (cxHessian gbPot y).det :=
    ReciprocityTheory.AnForm.A.mdisc_const _
  simp only [maDensity, hmd, det_cxHessian_gbPot]
  have hG : (gbG y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (gbG_pos y).ne'
  have : (1 / ((2 : ℂ) ^ D * (gbG y : ℂ) ^ (D + 1))) = ((1 / ((2 : ℝ) ^ D * (gbG y) ^ (D + 1)) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.ofReal_re]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hGr : gbG y ≠ 0 := (gbG_pos y).ne'
  unfold gbG at hGr ⊢
  rw [div_pow]
  field_simp

theorem integral_maDensity_gbPot (D : ℕ) : ∫ y : Fin D → ℂ, maDensity (fun _ : Fin D => gbPot) y = 1 := by
  simp_rw [maDensity_gbPot]
  rw [integral_const_mul, gaM_integral_fsDens]
  have : (D.factorial : ℝ) ≠ 0 := by positivity
  have : Real.pi ^ D ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  field_simp

end FS

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
