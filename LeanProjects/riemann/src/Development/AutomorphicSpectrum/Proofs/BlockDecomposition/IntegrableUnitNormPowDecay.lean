import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulCIff

open MeasureTheory Matrix
open Ad3.K Ad3.K.LC Ad3.K.LC.C GlobalTheory.CompanionTheory.GodementFE

namespace GlobalTheory.CompanionTheory.GodementFE.Radial

theorem weight_eq (σ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖z‖ ^ (2 * (σ / 2) - 2) * dd z + ‖z‖ ^ (2 * ((σ + 1) / 2) - 2) * dd z =
      (‖z‖ ^ 2)⁻¹ * (‖z‖ ^ σ * dd z + ‖z‖ ^ (σ + 1) * dd z) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have e1 : (2 * (σ / 2) - 2) = σ - 2 := by ring
  have e2 : (2 * ((σ + 1) / 2) - 2) = (σ + 1) - 2 := by ring
  rw [e1, e2, Real.rpow_sub hp, Real.rpow_sub hp, Real.rpow_two]
  simp only [div_eq_mul_inv]
  ring

theorem integrable_weight : ∀ σ : ℝ, 0 < σ → σ < 1 →
    Integrable (fun a : ℂˣ => ‖(a : ℂ)‖ ^ σ * dd a + ‖(a : ℂ)‖ ^ (σ + 1) * dd a) mulC := by
  intro σ h0 h1
  have hA := (wt_vol (σ / 2) (by linarith) (by linarith)).add
    (wt_vol ((σ + 1) / 2) (by linarith) (by linarith))
  have hB : Integrable (fun z : ℂ => (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
      (((‖z‖ ^ σ * dd z + ‖z‖ ^ (σ + 1) * dd z : ℝ)) : ℂ)) := by
    refine (hA.ofReal (𝕜 := ℂ)).congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℂ))] with z hz
    have hz0 : z ≠ 0 := hz
    have := weight_eq σ hz0
    simp only [Pi.add_apply]
    rw [this]
    push_cast
    rfl
  have hF := (integrable_mulC_iff
    (fun z : ℂ => (((‖z‖ ^ σ * dd z + ‖z‖ ^ (σ + 1) * dd z : ℝ)) : ℂ))).2 hB
  simpa using hF.re

end GlobalTheory.CompanionTheory.GodementFE.Radial
