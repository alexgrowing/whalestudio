import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantScaled
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralKernelUniformBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MajorantLeSumSwap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateLocalL1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AestronglyMeasurableWhittakerDiagUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Ga
open MeasureTheory Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.MajC.TInt

open Ad3.K Ad3.K.LC Ad3.K.LC.B GlobalTheory.CompanionTheory.TateC

theorem integrable_mulC_real (g : ℂ → ℝ) :
    Integrable (fun a : ℂˣ => g a) mulC ↔ Integrable (fun x : ℂ => (‖x‖ ^ 2)⁻¹ • g x) volume := by
  have hd : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ 2)⁻¹ := by fun_prop
  have h2 : Integrable (fun a : ℂˣ => g a) mulC ↔
      Integrable g (Measure.map (Units.val : ℂˣ → ℂ) mulC) :=
    (val_measurableEmbedding.integrable_map_iff (g := g)).symm
  rw [h2, map_val_mulC, nuC,
    integrable_withDensity_iff_integrable_smul' hd (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  have : 0 ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  simp only [ENNReal.toReal_ofReal this]

theorem integral_mulC_real (g : ℂ → ℝ) :
    ∫ a : ℂˣ, g a ∂mulC = ∫ x : ℂ, (‖x‖ ^ 2)⁻¹ • g x := by
  have h1 : ∫ a : ℂˣ, g a ∂mulC = ∫ x, g x ∂nuC := by
    rw [← map_val_mulC, val_measurableEmbedding.integral_map]
  rw [h1, nuC, integral_withDensity_eq_integral_toReal_smul₀ (by fun_prop) (by simp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have : 0 ≤ (‖x‖ ^ 2)⁻¹ := by positivity
  simp only [ENNReal.toReal_ofReal this]

theorem density_le (σ : ℝ) (hσ : σ < 1) (N : ℕ) (hN : 4 - 4 * σ ≤ N) (q : ℝ) (hq : 0 < q)
    (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ (2 * σ - 2) / (1 + ‖z⁻¹‖ * q) ^ N) ≤
      q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hb := radial_bound (2 - 2 * σ) q ‖z‖ N (by linarith) hq hr (by linarith)
  have e1 : ‖z‖ ^ (-(2 + (2 - 2 * σ))) = (‖z‖ ^ 2)⁻¹ * ‖z‖ ^ (2 * σ - 2) := by
    rw [show -(2 + (2 - 2 * σ)) = (-2 : ℝ) + (2 * σ - 2) by ring, Real.rpow_add hr,
      Real.rpow_neg hr.le, Real.rpow_two]
  have e2 : ‖z⁻¹‖ * q = q / ‖z‖ := by
    rw [norm_inv]
    field_simp
  have e3 : -(2 - 2 * σ) = 2 * σ - 2 := by ring
  have hk : kern (2 - 2 * σ) q z =
      (‖z‖ ^ 2)⁻¹ * min ((‖z‖ / q) ^ (2 - 2 * σ)) ((q / ‖z‖) ^ (2 - 2 * σ)) := rfl
  rw [e1, e3] at hb
  rw [e2, hk, div_eq_mul_inv, ← mul_assoc]
  exact hb

theorem measurable_kern (s T : ℝ) : Measurable (kern s T) := by
  unfold kern
  fun_prop

theorem tint : ∀ σ : ℝ, σ < 1 → ∀ N : ℕ, 4 - 4 * σ ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℂˣ => ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N) Ad3.K.mulC ∧
    ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N ∂Ad3.K.mulC ≤
      K * q ^ (2 * σ - 2) := by
  intro σ hσ N hN
  obtain ⟨K, hK0, hK⟩ := KernInt.lintegral_kern_le (2 - 2 * σ) (by linarith)
  refine ⟨K, fun q hq => ?_⟩
  set g : ℂ → ℝ := fun z => ‖z‖ ^ (2 * σ - 2) / (1 + ‖z⁻¹‖ * q) ^ N with hg
  have hkm := measurable_kern (2 - 2 * σ) q
  have hk0 : ∀ z, 0 ≤ kern (2 - 2 * σ) q z := kern_nonneg' _ _ hq
  have hfin : ∫⁻ z : ℂ, ENNReal.ofReal (kern (2 - 2 * σ) q z) < ⊤ :=
    (hK q hq).trans_lt ENNReal.ofReal_lt_top
  have hkI : Integrable (kern (2 - 2 * σ) q) volume := by
    refine ⟨hkm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hk0)]
    exact hfin
  have hkint : ∫ z : ℂ, kern (2 - 2 * σ) q z ≤ K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hk0) hkm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 (hK q hq)
  have hqp : 0 ≤ q ^ (2 * σ - 2) := (Real.rpow_pos_of_pos hq _).le
  have hae : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))
  have hgm : Measurable fun z : ℂ => (‖z‖ ^ 2)⁻¹ • g z := by
    simp only [hg]
    fun_prop
  have hg0 : ∀ z : ℂ, 0 ≤ (‖z‖ ^ 2)⁻¹ • g z := by
    intro z
    have : 0 ≤ ‖z‖ ^ (2 * σ - 2) := Real.rpow_nonneg (norm_nonneg _) _
    simp only [hg, smul_eq_mul]
    positivity
  have hle : ∀ᵐ z : ℂ, (‖z‖ ^ 2)⁻¹ • g z ≤ q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z := by
    filter_upwards [hae] with z hz
    exact density_le σ hσ N hN q hq z hz
  have hbI : Integrable (fun z : ℂ => q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z) volume :=
    hkI.const_mul _
  have hI : Integrable (fun z : ℂ => (‖z‖ ^ 2)⁻¹ • g z) volume := by
    refine hbI.mono' hgm.aestronglyMeasurable ?_
    filter_upwards [hle] with z hz
    rw [Real.norm_of_nonneg (hg0 z)]
    exact hz
  refine ⟨(integrable_mulC_real g).2 hI, ?_⟩
  have e := integral_mulC_real g
  calc ∫ t : ℂˣ, ‖(t : ℂ)‖ ^ (2 * σ - 2) / (1 + ‖(t : ℂ)⁻¹‖ * q) ^ N ∂Ad3.K.mulC
      = ∫ z : ℂ, (‖z‖ ^ 2)⁻¹ • g z := e
    _ ≤ ∫ z : ℂ, q ^ (2 * σ - 2) * kern (2 - 2 * σ) q z := integral_mono_ae hI hbI hle
    _ = q ^ (2 * σ - 2) * ∫ z : ℂ, kern (2 - 2 * σ) q z := integral_const_mul _ _
    _ ≤ q ^ (2 * σ - 2) * K := mul_le_mul_of_nonneg_left hkint hqp
    _ = K * q ^ (2 * σ - 2) := mul_comm _ _

end GlobalTheory.CompanionTheory.MajC.TInt
