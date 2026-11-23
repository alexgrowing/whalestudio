import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightRealStatement

open MeasureTheory

namespace GlobalTheory.CompanionTheory.RealTateConv

theorem integrable_mulR_abs_rpow_mul_one_add_rpow_neg :
    ∀ (q N : ℝ), 0 < q → q < N →
      MeasureTheory.Integrable (fun a : ℝˣ => |(a : ℝ)| ^ q * (1 + |(a : ℝ)|) ^ (-N)) Ad3.mulR := by
  intro q N hq hN
  have h := GlobalTheory.T.integrable_power_weight_real (q - 1) N (by linarith) (by linarith)
  let g : ℝ → ℂ := fun x => ((|x| ^ q * (1 + |x|) ^ (-N) : ℝ) : ℂ)
  have key : Integrable (fun x : ℝ => |x|⁻¹ • g x) volume := by
    have hc : Integrable (fun x : ℝ => ((|x| ^ (q - 1) * (1 + |x|) ^ (-N) : ℝ) : ℂ)) volume :=
      h.ofReal
    refine hc.congr ?_
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
    have hpos : 0 < |x| := abs_pos.2 hx
    simp only [g]
    rw [Real.rpow_sub_one hpos.ne', Complex.real_smul]
    push_cast
    ring
  have h2 := ((integrable_mulR_iff g).2 key).re
  simpa [g] using h2

end GlobalTheory.CompanionTheory.RealTateConv
