import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.FunctionalEquationGL2GL1Complex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePhi

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PowerKernel

noncomputable def dens (σ : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  |y|⁻¹ * (|y| ^ (σ - 1) / (1 + |y⁻¹| * 1) ^ N)

theorem measurable_dens (σ : ℝ) (N : ℕ) : Measurable (dens σ N) := by
  unfold dens
  have h1 : Measurable fun y : ℝ => |y| := by fun_prop
  have h2 : Measurable fun y : ℝ => |y| ^ (σ - 1) := h1.pow_const _
  have h3 : Measurable fun y : ℝ => (1 + |y⁻¹| * 1) ^ N := by fun_prop
  exact (h1.inv).mul (h2.div h3)

theorem dens_nonneg (σ : ℝ) (N : ℕ) (y : ℝ) : 0 ≤ dens σ N y := by
  unfold dens
  positivity

theorem dens_neg (σ : ℝ) (N : ℕ) (y : ℝ) : dens σ N (-y) = dens σ N y := by
  simp [dens, inv_neg, abs_neg]

theorem dens_le_small (σ : ℝ) {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 0 < y) :
    dens σ N y ≤ y ^ (σ - 1) := by
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hp : 0 < y ^ (σ - 1) := Real.rpow_pos_of_pos hy _
  have hb : y⁻¹ ≤ (1 + y⁻¹) ^ N := by
    calc y⁻¹ ≤ 1 + y⁻¹ := by linarith
      _ = (1 + y⁻¹) ^ 1 := (pow_one _).symm
      _ ≤ (1 + y⁻¹) ^ N := pow_le_pow_right₀ (by linarith) hN
  have hD : 0 < (1 + y⁻¹) ^ N := by positivity
  simp only [dens, abs_of_pos hy, abs_of_pos hyi, mul_one]
  rw [← mul_div_assoc, div_le_iff₀ hD, mul_comm]
  exact mul_le_mul_of_nonneg_left hb hp.le

theorem dens_le_large (σ : ℝ) (N : ℕ) {y : ℝ} (hy : 0 < y) :
    dens σ N y ≤ y ^ (σ - 2) := by
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hp : 0 < y ^ (σ - 1) := Real.rpow_pos_of_pos hy _
  have hb : 1 ≤ (1 + y⁻¹) ^ N := one_le_pow₀ (by linarith)
  have he : y ^ (σ - 2) = y⁻¹ * y ^ (σ - 1) := by
    rw [show σ - 2 = -1 + (σ - 1) by ring, Real.rpow_add hy, Real.rpow_neg_one]
  simp only [dens, abs_of_pos hy, abs_of_pos hyi, mul_one]
  rw [he]
  exact mul_le_mul_of_nonneg_left (div_le_self hp.le hb) hyi.le

theorem dens_integrableOn {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (dens σ N) (Ioi 0) := by
  have hA : IntegrableOn (dens σ N) (Ioc 0 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (σ - 1)) (Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := σ - 1) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine Integrable.mono' hi (measurable_dens σ N).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_of_nonneg (dens_nonneg σ N y)]
    exact dens_le_small σ hN hy.1
  have hB : IntegrableOn (dens σ N) (Ioi 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (σ - 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine Integrable.mono' hi (measurable_dens σ N).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_of_nonneg (dens_nonneg σ N y)]
    exact dens_le_large σ N (lt_trans zero_lt_one hy)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  exact hA.union hB

theorem dens_integrable {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (dens σ N) := by
  have hI : Integrable ((Ioi (0 : ℝ)).indicator (dens σ N)) :=
    (dens_integrableOn h0 h1 hN).integrable_indicator measurableSet_Ioi
  have hJ : Integrable fun x : ℝ => (Ioi (0 : ℝ)).indicator (dens σ N) (-x) := hI.comp_neg
  refine (hI.add hJ).congr (Filter.Eventually.of_forall fun x => ?_)
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h2 : x ∉ Ioi (0 : ℝ) := by simp [hx.le]
    have h3 : -x ∈ Ioi (0 : ℝ) := by simpa using hx
    simp [Set.indicator_of_notMem h2, Set.indicator_of_mem h3, dens_neg]
  · subst hx
    simp [dens]
  · have h2 : x ∈ Ioi (0 : ℝ) := hx
    have h3 : -x ∉ Ioi (0 : ℝ) := by simp [hx.le]
    simp [Set.indicator_of_mem h2, Set.indicator_of_notMem h3]

theorem kernel_one_integrable {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) Ad3.mulR := by
  have key : Integrable (fun x : ℝ => |x|⁻¹ •
      (((|x| ^ (σ - 1) / (1 + |x⁻¹| * 1) ^ N : ℝ)) : ℂ)) volume := by
    refine ((dens_integrable h0 h1 hN).ofReal (𝕜 := ℂ)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [dens, Complex.real_smul]
  exact ((GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_iff
    (fun x : ℝ => (((|x| ^ (σ - 1) / (1 + |x⁻¹| * 1) ^ N : ℝ)) : ℂ))).2 key).re

theorem kernel_scale (σ : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q) (t : ℝˣ) :
    |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)| ^ (σ - 1) /
        (1 + |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)⁻¹| * q) ^ N =
      q ^ (σ - 1) * (|(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) := by
  have h1 : |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)| = |(t : ℝ)| * q := by
    simp [abs_mul, abs_of_pos hq]
  have h2 : |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)⁻¹| * q = |(t : ℝ)⁻¹| * 1 := by
    simp only [Units.val_mul, Units.val_mk0, mul_inv, abs_mul, abs_inv, abs_of_pos hq]
    field_simp
  rw [h1, h2, Real.mul_rpow (abs_nonneg _) hq.le]
  ring

theorem kernel_integral_le :
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N) Ad3.mulR ∧
    ∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N ∂Ad3.mulR ≤ K * q ^ (σ - 1) := by
  intro σ h0 h1 N hN
  refine ⟨∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N ∂Ad3.mulR, fun q hq => ?_⟩
  set u : ℝˣ := Units.mk0 q hq.ne' with hu
  set f : ℝˣ → ℝ := fun t => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N with hf
  have hcomp : (fun t : ℝˣ => f (t * u)) = fun t : ℝˣ =>
      q ^ (σ - 1) * (|(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) := by
    funext t
    exact kernel_scale σ N hq t
  have hint : Integrable (fun t : ℝˣ => f (t * u)) Ad3.mulR := by
    rw [hcomp]
    exact (kernel_one_integrable h0 h1 hN).const_mul _
  have hfi : Integrable f Ad3.mulR := by
    have := hint.comp_mul_right u⁻¹
    simpa using this
  refine ⟨hfi, le_of_eq ?_⟩
  rw [← integral_mul_right_eq_self f u, hcomp, integral_const_mul, mul_comm]

end GlobalTheory.CompanionTheory.PowerKernel
