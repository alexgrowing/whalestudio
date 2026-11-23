import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern

noncomputable section

open MeasureTheory Matrix Set GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

namespace GlobalTheory.CompanionTheory.MajC.KernInt

lemma lintegral_lo {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    ∫⁻ r in Ioc (0 : ℝ) T, ENNReal.ofReal (r ^ (s - 1) * T ^ (-s)) = ENNReal.ofReal (1 / s) := by
  have hint : IntervalIntegrable (fun r : ℝ => r ^ (s - 1)) volume 0 T :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hI : IntegrableOn (fun r : ℝ => r ^ (s - 1) * T ^ (-s)) (Ioc 0 T) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hint).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hI ?_]
  · congr 1
    rw [integral_mul_const, ← intervalIntegral.integral_of_le hT.le,
      integral_rpow (Or.inl (by linarith))]
    have h1 : s - 1 + 1 = s := by ring
    have hp : T ^ s ≠ 0 := (Real.rpow_pos_of_pos hT s).ne'
    rw [h1, Real.zero_rpow hs.ne', sub_zero, Real.rpow_neg hT.le]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg hT.le _)

lemma lintegral_hi {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    ∫⁻ r in Ioi T, ENNReal.ofReal (r ^ (-s - 1) * T ^ s) = ENNReal.ofReal (1 / s) := by
  have ha : -s - 1 < -1 := by linarith
  have hI : IntegrableOn (fun r : ℝ => r ^ (-s - 1) * T ^ s) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt ha hT).mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hI ?_]
  · congr 1
    rw [integral_mul_const, integral_Ioi_rpow_of_lt ha hT]
    have h1 : -s - 1 + 1 = -s := by ring
    have hp : T ^ s ≠ 0 := (Real.rpow_pos_of_pos hT s).ne'
    rw [h1, Real.rpow_neg hT.le]
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have : 0 < r := hT.trans hr
    exact mul_nonneg (Real.rpow_nonneg this.le _) (Real.rpow_nonneg hT.le _)

def prof (s T r : ℝ) : ℝ := r * ((r ^ 2)⁻¹ * min ((r / T) ^ s) ((T / r) ^ s))

lemma measurable_prof (s T : ℝ) : Measurable (prof s T) := by
  unfold prof
  fun_prop

lemma prof_le_lo {s T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    prof s T r ≤ r ^ (s - 1) * T ^ (-s) := by
  unfold prof
  have h1 : r * (r ^ 2)⁻¹ = r⁻¹ := by field_simp
  have h2 : r ^ (s - 1) * T ^ (-s) = r⁻¹ * (r / T) ^ s := by
    rw [Real.rpow_sub_one hr.ne', Real.div_rpow hr.le hT.le, Real.rpow_neg hT.le]
    field_simp
  rw [← mul_assoc, h1, h2]
  exact mul_le_mul_of_nonneg_left (min_le_left _ _) (inv_nonneg.2 hr.le)

lemma prof_le_hi {s T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    prof s T r ≤ r ^ (-s - 1) * T ^ s := by
  unfold prof
  have h1 : r * (r ^ 2)⁻¹ = r⁻¹ := by field_simp
  have h2 : r ^ (-s - 1) * T ^ s = r⁻¹ * (T / r) ^ s := by
    rw [Real.rpow_sub_one hr.ne', Real.div_rpow hT.le hr.le, Real.rpow_neg hr.le]
    field_simp
  rw [← mul_assoc, h1, h2]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) (inv_nonneg.2 hr.le)

lemma lintegral_prof_le {s T : ℝ} (hs : 0 < s) (hT : 0 < T) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (prof s T r) ≤ ENNReal.ofReal (2 / s) := by
  rw [← Ioc_union_Ioi_eq_Ioi hT.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hlo : ∫⁻ r in Ioc (0 : ℝ) T, ENNReal.ofReal (prof s T r) ≤ ENNReal.ofReal (1 / s) := by
    rw [← lintegral_lo hs hT]
    exact setLIntegral_mono' measurableSet_Ioc fun r hr =>
      ENNReal.ofReal_le_ofReal (prof_le_lo hT hr.1)
  have hhi : ∫⁻ r in Ioi T, ENNReal.ofReal (prof s T r) ≤ ENNReal.ofReal (1 / s) := by
    rw [← lintegral_hi hs hT]
    exact setLIntegral_mono' measurableSet_Ioi fun r hr =>
      ENNReal.ofReal_le_ofReal (prof_le_hi hT (hT.trans hr))
  have h2 : ENNReal.ofReal (2 / s) = ENNReal.ofReal (1 / s) + ENNReal.ofReal (1 / s) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [h2]
  exact add_le_add hlo hhi

theorem lintegral_kern_le : ∀ s : ℝ, 0 < s → ∃ K : ℝ, 0 ≤ K ∧ ∀ T₀ : ℝ, 0 < T₀ →
    ∫⁻ z : ℂ, ENNReal.ofReal (kern s T₀ z) ≤ ENNReal.ofReal K := by
  intro s hs
  refine ⟨2 / s * (2 * Real.pi), by positivity, fun T hT => ?_⟩
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hcongr : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (kern s T (Complex.polarCoord.symm p)) =
      ∫⁻ p in polarCoord.target, ENNReal.ofReal (prof s T p.1) := by
    refine setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo |> fun h => by
      rw [polarCoord_target]; exact h) fun p hp => ?_
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    simp only [smul_eq_mul, kern, hn, prof]
    rw [ENNReal.ofReal_mul hp1.le]
  rw [hcongr, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hprod := lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioo (-Real.pi) Real.pi))
    (f := fun r => ENNReal.ofReal (prof s T r)) (g := fun _ => (1 : ENNReal))
    (measurable_prof s T).ennreal_ofReal.aemeasurable aemeasurable_const
  simp only [mul_one] at hprod
  rw [hprod, lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioo,
    ENNReal.ofReal_mul (by positivity)]
  have h2 : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [h2]
  exact mul_le_mul_left (lintegral_prof_le hs hT) _

end GlobalTheory.CompanionTheory.MajC.KernInt
