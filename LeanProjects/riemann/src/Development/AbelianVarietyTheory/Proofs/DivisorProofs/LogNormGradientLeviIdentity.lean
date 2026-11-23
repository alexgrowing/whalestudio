import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogPotentialFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtLogNorm
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.LeviGradCoord

theorem grad_sq_mul_eq_levi : ∀ {e : ℕ} (h : (Fin e → ℂ) → ℂ) (Φ N : (Fin e → ℂ) → ℝ) (z w : Fin e → ℂ),
    AnalyticAt ℂ h z → h z ≠ 0 → ContDiffAt ℝ 2 Φ z →
    N =ᶠ[nhds z] (fun y => ‖h y‖ ^ 2 * Real.exp (-2 * Φ y)) →
    ((fderiv ℝ (fun y => Real.exp 1 - Real.log (N y)) z w) ^ 2 +
      (fderiv ℝ (fun y => Real.exp 1 - Real.log (N y)) z (Complex.I • w)) ^ 2) / 4 * N z =
      levi N z w + 2 * N z * levi Φ z w := by
  intro e h Φ N z w hh h0 hΦ hN
  have hL : ContDiffAt ℝ 2 (fun y => Real.log ‖h y‖) z :=
    (GlobalTheory.Mean4O.BdSec.contDiffAt_log_norm hh h0).of_le two_le_infty
  have hL2 : ContDiffAt ℝ 2 (fun y => 2 * Real.log ‖h y‖) z := contDiffAt_const.mul hL
  have hΦ2 : ContDiffAt ℝ 2 (fun y => (-2) * Φ y) z := contDiffAt_const.mul hΦ
  have hFc : ContDiffAt ℝ 2 (fun y => 2 * Real.log ‖h y‖ + (-2) * Φ y) z := hL2.add hΦ2
  have hne : ∀ᶠ y in 𝓝 z, h y ≠ 0 := hh.continuousAt.eventually_ne h0
  have hNF : N =ᶠ[𝓝 z] fun y => Real.exp (2 * Real.log ‖h y‖ + (-2) * Φ y) := by
    filter_upwards [hN, hne] with y hy hy0
    have hp : (0 : ℝ) < ‖h y‖ := norm_pos_iff.2 hy0
    have h2 : Real.exp (2 * Real.log ‖h y‖) = ‖h y‖ ^ 2 := by
      rw [show (2 : ℝ) * Real.log ‖h y‖ = Real.log (‖h y‖ ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [hy, Real.exp_add, h2]
  have hNc : ContDiffAt ℝ 2 N z :=
    (Real.contDiff_exp.contDiffAt.comp z hFc).congr_of_eventuallyEq hNF
  have hpos : 0 < N z := by rw [hNF.eq_of_nhds]; exact Real.exp_pos _
  have hlogF : (fun y => Real.log (N y)) =ᶠ[𝓝 z] fun y => 2 * Real.log ‖h y‖ + (-2) * Φ y :=
    hNF.mono fun y hy => by simp only at hy ⊢; rw [hy, Real.log_exp]
  have hlevi : levi (fun y => Real.log (N y)) z w = -2 * levi Φ z w := by
    rw [ReciprocityTheory.AnForm.levi_congr hlogF w, GlobalTheory.LeviLogChain.levi_add_of hL2 hΦ2 w,
      GlobalTheory.LeviLogChain.levi_const_mul_of _ hL w, GlobalTheory.LeviLogChain.levi_const_mul_of _ hΦ w,
      GlobalTheory.Mean4O.BdSec.levi_log_norm hh h0 w]
    ring
  have hchain := GlobalTheory.LeviLogChain.levi_log hNc hpos w
  rw [hlevi] at hchain
  have hD : HasFDerivAt (fun y => Real.exp 1 - Real.log (N y)) (-((N z)⁻¹ • fderiv ℝ N z)) z :=
    ((hNc.differentiableAt (by norm_num)).hasFDerivAt.log hpos.ne').const_sub (Real.exp 1)
  rw [hD.fderiv]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hN0 : N z ≠ 0 := hpos.ne'
  field_simp at hchain ⊢
  linear_combination hchain

end GlobalTheory.LeviGradCoord
