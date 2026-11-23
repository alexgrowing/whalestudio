import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Kern

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC Ad3.K.LC.B

noncomputable section

namespace GlobalTheory.CompanionTheory.MajGm

theorem measurable_kern (s T : ℝ) : Measurable (kern s T) := by
  unfold kern
  refine Measurable.mul (by fun_prop) (Measurable.min (by fun_prop) (by fun_prop))

theorem measurable_gm (ε β : ℝ) (m : ℕ) : Measurable (gm ε β m) := by
  unfold gm
  have hk := measurable_kern ε β
  refine Measurable.ite ?_ ?_ (by fun_prop)
  · have h1 : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {h : M22 | h 0 0 ≠ 0} :=
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
    exact h1.inter h2
  · refine Measurable.mul (by fun_prop) (hk.comp (by fun_prop))

theorem kern_nonneg (s T : ℝ) (hT : 0 < T) (z : ℂ) : 0 ≤ kern s T z := by
  unfold kern
  have h1 : 0 ≤ ‖z‖ / T := by positivity
  have h2 : 0 ≤ T / ‖z‖ := by positivity
  exact mul_nonneg (by positivity)
    (le_min (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _))

theorem real_bound (ε r : ℝ) (m : ℕ) (hε : 0 < ε) (hm : 2 * ε ≤ m) (hr : 0 < r) :
    r ^ (-4 + ε) * ((1 + r) ^ m)⁻¹ * r ^ 2 ≤ (r ^ 2)⁻¹ * min ((r / 1) ^ ε) ((1 / r) ^ ε) := by
  have e1 : r ^ (-4 + ε) * r ^ 2 = (r ^ 2)⁻¹ * r ^ ε := by
    rw [Real.rpow_add hr, show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hr.le,
      Real.rpow_natCast]
    field_simp
  have hw0 : 0 < ((1 + r) ^ m)⁻¹ := by positivity
  have hw1 : ((1 + r) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hrε : 0 < r ^ ε := Real.rpow_pos_of_pos hr _
  have key : r ^ ε * ((1 + r) ^ m)⁻¹ ≤ min ((r / 1) ^ ε) ((1 / r) ^ ε) := by
    refine le_min ?_ ?_
    · rw [div_one]
      exact mul_le_of_le_one_right hrε.le hw1
    · rcases le_total r 1 with h | h
      · have : r ≤ 1 / r := by
          rw [le_div_iff₀ hr]
          nlinarith
        calc r ^ ε * ((1 + r) ^ m)⁻¹ ≤ r ^ ε := mul_le_of_le_one_right hrε.le hw1
          _ ≤ (1 / r) ^ ε := Real.rpow_le_rpow hr.le this hε.le
      · have h2 : r ^ (2 * ε) ≤ (1 + r) ^ m := by
          calc r ^ (2 * ε) ≤ r ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le h hm
            _ = r ^ m := Real.rpow_natCast _ _
            _ ≤ (1 + r) ^ m := pow_le_pow_left₀ hr.le (by linarith) _
        have h3 : (1 / r) ^ ε = (r ^ ε)⁻¹ := by
          rw [one_div, Real.inv_rpow hr.le]
        have h4 : r ^ (2 * ε) = r ^ ε * r ^ ε := by
          rw [two_mul, Real.rpow_add hr]
        rw [h4] at h2
        rw [h3, ← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div,
          le_div_iff₀ hrε]
        exact h2
  calc r ^ (-4 + ε) * ((1 + r) ^ m)⁻¹ * r ^ 2
      = (r ^ (-4 + ε) * r ^ 2) * ((1 + r) ^ m)⁻¹ := by ring
    _ = (r ^ 2)⁻¹ * (r ^ ε * ((1 + r) ^ m)⁻¹) := by rw [e1]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by positivity)

theorem finite_Q (m : ℕ) (hm : 3 ≤ m) :
    ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) < ⊤ := by
  have h : Integrable (fun x : ℂ => (1 + ‖x‖) ^ (-(m : ℝ))) volume := by
    apply integrable_one_add_norm
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    simp only [Complex.finrank_real_complex]
    push_cast
    linarith
  have h2 := h.lintegral_lt_top
  refine lt_of_le_of_lt (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem lint_rows (F : M22 → ENNReal) (hF : Measurable F) :
    ∫⁻ h, F h = ∫⁻ a : ℂ × ℂ, ∫⁻ v : ℂ, ∫⁻ y : ℂ, F ![![a.1, a.2], ![v, y]] := by
  have e2 := volume_preserving_piFinTwo (fun _ : Fin 2 => ℂ)
  have e1 := volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℂ)
  have P := (e1.symm _).comp ((e2.symm _).prod (e2.symm _))
  have hΦ : (⇑(MeasurableEquiv.piFinTwo fun _ : Fin 2 => Fin 2 → ℂ).symm ∘
      Prod.map (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℂ).symm
        (MeasurableEquiv.piFinTwo fun _ : Fin 2 => ℂ).symm) =
      fun p : (ℂ × ℂ) × (ℂ × ℂ) => (![![p.1.1, p.1.2], ![p.2.1, p.2.2]] : M22) := by
    funext p
    funext i j
    fin_cases i <;> fin_cases j <;> simp [MeasurableEquiv.piFinTwo]
  rw [hΦ] at P
  have hG : Measurable fun p : (ℂ × ℂ) × (ℂ × ℂ) =>
      F (![![p.1.1, p.1.2], ![p.2.1, p.2.2]] : M22) := hF.comp P.measurable
  rw [← P.lintegral_comp hF, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun a => ?_
  have hG2 : Measurable fun b : ℂ × ℂ => F (![![a.1, a.2], ![b.1, b.2]] : M22) :=
    hG.comp (measurable_prodMk_left (x := a))
  rw [Measure.volume_eq_prod, lintegral_prod _ hG2.aemeasurable]

theorem inner_le (ε K β : ℝ) (m : ℕ) (hε : 0 < ε) (hK : 0 ≤ K) (hβ : 0 < β)
    (hker : ∫⁻ z : ℂ, ENNReal.ofReal (kern ε β z) ≤ ENNReal.ofReal K) (hm : 2 * ε ≤ m)
    (u x : ℂ) :
    ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![u, x], ![v, y]]) ≤
      ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 u) *
        ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) := by
  by_cases hu : u = 0
  · subst hu
    simp [gm]
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hβε : 0 < β ^ (-ε) := Real.rpow_pos_of_pos hβ _
  have hP : 0 < ‖u‖ ^ (-4 + ε) := Real.rpow_pos_of_pos hr _
  have hb : 0 < ((1 + ‖x‖) ^ m)⁻¹ := by positivity
  have hw : 0 < ((1 + ‖u‖) ^ m)⁻¹ := by positivity
  set A : ℝ := β ^ (-ε) * ‖u‖ ^ (-4 + ε) * ((1 + ‖u‖) ^ m)⁻¹ * ((1 + ‖x‖) ^ m)⁻¹ with hAdef
  have hA : 0 ≤ A := by positivity
  have h1 : ∀ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![u, x], ![v, y]]) ≤
      (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := by
    intro v
    by_cases hv : ‖v‖ ≤ ‖u‖
    · rw [Set.indicator_of_mem (by simpa using hv)]
      have e : ∀ y : ℂ, gm ε β m ![![u, x], ![v, y]] = A * kern ε β (y - v / u * x) := by
        intro y
        simp [gm, hv, hu, hAdef]
      simp_rw [e, ENNReal.ofReal_mul hA]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      rw [lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (kern ε β z)) (v / u * x)]
      exact hker
    · have e : ∀ y : ℂ, gm ε β m ![![u, x], ![v, y]] = 0 := by
        intro y
        simp [gm, hv]
      simp [e]
  have hvol : volume (Metric.closedBall (0 : ℂ) ‖u‖) = ENNReal.ofReal (‖u‖ ^ 2 * Real.pi) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hr.le]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    simp
  have hreal := real_bound ε ‖u‖ m hε hm hr
  have hkn := kern_nonneg ε 1 one_pos u
  have hfin : A * K * (‖u‖ ^ 2 * Real.pi) ≤
      β ^ (-ε) * Real.pi * K * kern ε 1 u * ((1 + ‖x‖) ^ m)⁻¹ := by
    have hc : 0 ≤ β ^ (-ε) * Real.pi * K * ((1 + ‖x‖) ^ m)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hreal hc
    calc A * K * (‖u‖ ^ 2 * Real.pi)
        = β ^ (-ε) * Real.pi * K * ((1 + ‖x‖) ^ m)⁻¹ *
            (‖u‖ ^ (-4 + ε) * ((1 + ‖u‖) ^ m)⁻¹ * ‖u‖ ^ 2) := by rw [hAdef]; ring
      _ ≤ _ := this
      _ = _ := by unfold kern; ring
  calc ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![u, x], ![v, y]])
      ≤ ∫⁻ v : ℂ, (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := lintegral_mono h1
    _ = ENNReal.ofReal A * ENNReal.ofReal K * volume (Metric.closedBall (0 : ℂ) ‖u‖) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
    _ = ENNReal.ofReal (A * K * (‖u‖ ^ 2 * Real.pi)) := by
        rw [hvol, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hK)]
    _ ≤ ENNReal.ofReal (β ^ (-ε) * Real.pi * K * kern ε 1 u * ((1 + ‖x‖) ^ m)⁻¹) :=
        ENNReal.ofReal_le_ofReal hfin
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]

theorem gm_integral_le : ∀ (ε K : ℝ) (m : ℕ), 0 < ε → 0 ≤ K →
    (∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern ε T₀ z) ≤ ENNReal.ofReal K) →
    3 ≤ m → 2 * ε ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 < β →
      ∫⁻ h : M22, ENNReal.ofReal (gm ε β m h) ≤ ENNReal.ofReal (C * β ^ (-ε)) := by
  intro ε K m hε hK hker hm3 hm
  have hQ := finite_Q m hm3
  set Q : ENNReal := ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) with hQdef
  refine ⟨Real.pi * K * K * Q.toReal, by positivity, fun β hβ => ?_⟩
  have hβε : 0 < β ^ (-ε) := Real.rpow_pos_of_pos hβ _
  have hmeas : Measurable fun h : M22 => ENNReal.ofReal (gm ε β m h) :=
    (measurable_gm ε β m).ennreal_ofReal
  have hf : Measurable fun u : ℂ =>
      ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 u) :=
    ((measurable_kern ε 1).ennreal_ofReal).const_mul _
  have hg : Measurable fun x : ℂ => ENNReal.ofReal (((1 + ‖x‖) ^ m)⁻¹) := by
    refine Measurable.ennreal_ofReal ?_
    fun_prop
  rw [lint_rows _ hmeas]
  calc ∫⁻ a : ℂ × ℂ, ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (gm ε β m ![![a.1, a.2], ![v, y]])
      ≤ ∫⁻ a : ℂ × ℂ, (ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 a.1)) *
          ENNReal.ofReal (((1 + ‖a.2‖) ^ m)⁻¹) :=
        lintegral_mono fun a => inner_le ε K β m hε hK hβ (hker β hβ) hm a.1 a.2
    _ = (∫⁻ u : ℂ, ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal (kern ε 1 u)) * Q := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable
    _ ≤ (ENNReal.ofReal (β ^ (-ε) * Real.pi * K) * ENNReal.ofReal K) * Q := by
        rw [lintegral_const_mul _ (measurable_kern ε 1).ennreal_ofReal]
        gcongr
        exact hker 1 one_pos
    _ = ENNReal.ofReal (Real.pi * K * K * Q.toReal * β ^ (-ε)) := by
        have hQt : Q = ENNReal.ofReal Q.toReal := (ENNReal.ofReal_toReal hQ.ne).symm
        conv_lhs => rw [hQt]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end GlobalTheory.CompanionTheory.MajGm
