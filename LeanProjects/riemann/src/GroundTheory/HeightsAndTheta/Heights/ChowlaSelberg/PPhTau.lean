import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic MeasureTheory ZSpan
open scoped Real ModularForm UpperHalfPlane

noncomputable section

theorem latticeArea_latticeOfTau (τ : ℍ) : latticeArea (latticeOfTau τ).lattice = τ.im := by
  have hvol : volume.real (fundamentalDomain Complex.basisOneI) = 1 := by
    rw [← Complex.toBasis_orthonormalBasisOneI,
      measureReal_congr (fundamentalDomain_ae_parallelepiped _ volume)]
    rw [measureReal_def, OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
    simp
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ (latticeOfTau τ).latticeBasis
    Complex.basisOneI, hvol, mul_one, Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr, abs_of_pos τ.im_pos]

theorem PhTau.proof (hΔ : DeltaEta.Statement) : PhTau.Statement := by
  intro τ
  have hy : 0 < τ.im := τ.im_pos
  have hη : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero (z := (τ : ℂ)) τ.im_pos
  have hn : 0 < ‖η (τ : ℂ)‖ := norm_pos_iff.2 hη
  have h1 : ‖((2 * π : ℝ) : ℂ) ^ 12 * η (τ : ℂ) ^ 24‖ = ((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring
  have h6 : (1 / 6 : ℝ) * Real.log (((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6) =
      Real.log ((2 * π) ^ 2 * ‖η (τ : ℂ)‖ ^ 4) := by
    rw [Real.log_pow]; push_cast; ring
  unfold logPeriod
  rw [latticeArea_latticeOfTau, hΔ τ, h1, h6, ← Real.log_mul (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
