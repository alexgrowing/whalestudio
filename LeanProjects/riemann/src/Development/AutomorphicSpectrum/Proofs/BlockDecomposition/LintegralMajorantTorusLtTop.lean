import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantScaled
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Ga
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralMajorantLePowNeg

open MeasureTheory Matrix GlobalTheory.CompanionTheory.MajC Ad3.K.LC

noncomputable section

namespace GlobalTheory.CompanionTheory.PerUC.GaInt

theorem measurable_ga (σ : ℝ) (m : ℕ) : Measurable (GlobalTheory.CompanionTheory.PerUC.ga σ m) := by
  unfold GlobalTheory.CompanionTheory.PerUC.ga kern
  refine Measurable.ite ?_ ?_ (by fun_prop)
  · have h1 : MeasurableSet {h : M22 | ‖h 1 0‖ ≤ ‖h 0 0‖} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {h : M22 | h 0 0 ≠ 0} :=
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
    exact h1.inter h2
  · refine Measurable.mul (by fun_prop) (Measurable.mul (by fun_prop)
      (Measurable.min (by fun_prop) (by fun_prop)))

theorem ga_nonneg (σ : ℝ) (m : ℕ) (h : M22) : 0 ≤ GlobalTheory.CompanionTheory.PerUC.ga σ m h := by
  unfold GlobalTheory.CompanionTheory.PerUC.ga
  split_ifs with hc
  · have hr : 0 < ‖h 0 0‖ := norm_pos_iff.mpr hc.2
    have := GlobalTheory.CompanionTheory.MajGm.kern_nonneg (1 - σ) ‖h 0 0‖ hr (h 1 1 - h 1 0 / h 0 0 * h 0 1)
    have h0 := Real.rpow_nonneg hr.le (-2 - 2 * σ)
    positivity
  · exact le_rfl

theorem inner_le (σ K : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hK : 0 ≤ K)
    (hker : ∀ T₀ : ℝ, 0 < T₀ → ∫⁻ z : ℂ, ENNReal.ofReal (kern (1 - σ) T₀ z) ≤ ENNReal.ofReal K)
    (u x : ℂ) :
    ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]]) ≤
      ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 u) *
        ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
  by_cases hu : u = 0
  · subst hu
    simp [GlobalTheory.CompanionTheory.PerUC.ga]
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hP : 0 < ‖u‖ ^ (-2 - 2 * σ) := Real.rpow_pos_of_pos hr _
  set A : ℝ := ‖u‖ ^ (-2 - 2 * σ) * ((1 + ‖u‖) ^ 4)⁻¹ * ((1 + ‖x‖) ^ 4)⁻¹ with hAdef
  have hA : 0 ≤ A := by positivity
  have h1 : ∀ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]]) ≤
      (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := by
    intro v
    by_cases hv : ‖v‖ ≤ ‖u‖
    · rw [Set.indicator_of_mem (by simpa using hv)]
      have e : ∀ y : ℂ, GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]] =
          A * kern (1 - σ) ‖u‖ (y - v / u * x) := by
        intro y
        simp [GlobalTheory.CompanionTheory.PerUC.ga, hv, hu, hAdef]
      simp_rw [e, ENNReal.ofReal_mul hA]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      rw [lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (kern (1 - σ) ‖u‖ z)) (v / u * x)]
      exact hker _ hr
    · have e : ∀ y : ℂ, GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]] = 0 := by
        intro y
        simp [GlobalTheory.CompanionTheory.PerUC.ga, hv]
      simp [e]
  have hvol : volume (Metric.closedBall (0 : ℂ) ‖u‖) = ENNReal.ofReal (‖u‖ ^ 2 * Real.pi) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow hr.le]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    simp
  have hreal := GlobalTheory.CompanionTheory.MajGm.real_bound (2 - 2 * σ) ‖u‖ 4 (by linarith)
    (by push_cast; linarith) hr
  rw [show (-4 + (2 - 2 * σ) : ℝ) = -2 - 2 * σ by ring] at hreal
  have hkn := GlobalTheory.CompanionTheory.MajGm.kern_nonneg (2 - 2 * σ) 1 one_pos u
  have hfin : A * K * (‖u‖ ^ 2 * Real.pi) ≤
      Real.pi * K * kern (2 - 2 * σ) 1 u * ((1 + ‖x‖) ^ 4)⁻¹ := by
    have hc : 0 ≤ Real.pi * K * ((1 + ‖x‖) ^ 4)⁻¹ := by positivity
    have := mul_le_mul_of_nonneg_left hreal hc
    calc A * K * (‖u‖ ^ 2 * Real.pi)
        = Real.pi * K * ((1 + ‖x‖) ^ 4)⁻¹ *
            (‖u‖ ^ (-2 - 2 * σ) * ((1 + ‖u‖) ^ 4)⁻¹ * ‖u‖ ^ 2) := by rw [hAdef]; ring
      _ ≤ _ := this
      _ = _ := by unfold kern; ring
  calc ∫⁻ v : ℂ, ∫⁻ y : ℂ, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![u, x], ![v, y]])
      ≤ ∫⁻ v : ℂ, (Metric.closedBall (0 : ℂ) ‖u‖).indicator
        (fun _ => ENNReal.ofReal A * ENNReal.ofReal K) v := lintegral_mono h1
    _ = ENNReal.ofReal A * ENNReal.ofReal K * volume (Metric.closedBall (0 : ℂ) ‖u‖) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
    _ = ENNReal.ofReal (A * K * (‖u‖ ^ 2 * Real.pi)) := by
        rw [hvol, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hK)]
    _ ≤ ENNReal.ofReal (Real.pi * K * kern (2 - 2 * σ) 1 u * ((1 + ‖x‖) ^ 4)⁻¹) :=
        ENNReal.ofReal_le_ofReal hfin
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]

theorem ga_integrable : ∀ σ : ℝ, 0 < σ → σ < 1 → Measurable (GlobalTheory.CompanionTheory.PerUC.ga σ 4) ∧
    (∀ h, 0 ≤ GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) ∧
    ∫⁻ h : Ad3.K.LC.M22, ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) < ⊤ := by
  intro σ hσ0 hσ1
  refine ⟨measurable_ga σ 4, ga_nonneg σ 4, ?_⟩
  obtain ⟨K, hK, hker⟩ := KernInt.lintegral_kern_le (1 - σ) (by linarith)
  obtain ⟨K', hK', hker'⟩ := KernInt.lintegral_kern_le (2 - 2 * σ) (by linarith)
  have hQ := GlobalTheory.CompanionTheory.MajGm.finite_Q 4 (by norm_num)
  have hmeas : Measurable fun h : M22 => ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 h) :=
    (measurable_ga σ 4).ennreal_ofReal
  have hf : Measurable fun u : ℂ =>
      ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 u) :=
    ((GlobalTheory.CompanionTheory.MajGm.measurable_kern (2 - 2 * σ) 1).ennreal_ofReal).const_mul _
  have hg : Measurable fun x : ℂ => ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
    refine Measurable.ennreal_ofReal ?_
    fun_prop
  rw [GlobalTheory.CompanionTheory.MajGm.lint_rows _ hmeas]
  calc ∫⁻ a : ℂ × ℂ, ∫⁻ v : ℂ, ∫⁻ y : ℂ,
        ENNReal.ofReal (GlobalTheory.CompanionTheory.PerUC.ga σ 4 ![![a.1, a.2], ![v, y]])
      ≤ ∫⁻ a : ℂ × ℂ, (ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 a.1)) *
          ENNReal.ofReal (((1 + ‖a.2‖) ^ 4)⁻¹) :=
        lintegral_mono fun a => inner_le σ K hσ0 hσ1 hK hker a.1 a.2
    _ = (∫⁻ u : ℂ, ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal (kern (2 - 2 * σ) 1 u)) *
          ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable
    _ ≤ (ENNReal.ofReal (Real.pi * K) * ENNReal.ofReal K') *
          ∫⁻ x : ℂ, ENNReal.ofReal (((1 + ‖x‖) ^ 4)⁻¹) := by
        rw [lintegral_const_mul _ (GlobalTheory.CompanionTheory.MajGm.measurable_kern (2 - 2 * σ) 1).ennreal_ofReal]
        gcongr
        exact hker' 1 one_pos
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hQ

end GlobalTheory.CompanionTheory.PerUC.GaInt
