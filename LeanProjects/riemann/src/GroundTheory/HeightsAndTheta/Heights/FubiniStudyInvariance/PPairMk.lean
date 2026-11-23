import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyInvariance.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ComplexConjugate Matrix ENNReal
open MeasureTheory Set MvPolynomial

noncomputable section

namespace FSInv

open CP

theorem PairMk.proof : PairMk.Statement := by
  intro N n P Q hP hQ v hv
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  have hPe : eval ((a : ℂ) • v) P = (a : ℂ) ^ n * eval v P :=
    evalAt_smul (RingHom.id ℂ) ((mem_homogeneousSubmodule _ _).mp hP) (a : ℂ) v
  have hQe : eval ((a : ℂ) • v) Q = (a : ℂ) ^ n * eval v Q :=
    evalAt_smul (RingHom.id ℂ) ((mem_homogeneousSubmodule _ _).mp hQ) (a : ℂ) v
  rw [fsPair, ← ha, Units.smul_def, hPe, hQe, euclideanNorm_smul]
  have ha0 : (a : ℂ) ≠ 0 := a.ne_zero
  have hA : ((‖(a : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr ha0).ne'
  have hN : ((norm2 v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (euclideanNorm_pos hv).ne'
  have hc : conj (a : ℂ) ^ n * (a : ℂ) ^ n = ((‖(a : ℂ)‖ : ℝ) : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.conj_mul', ← pow_mul]
  push_cast
  rw [div_eq_div_iff (pow_ne_zero _ (mul_ne_zero hA hN)) (pow_ne_zero _ hN), map_mul, map_pow,
    mul_pow, ← hc]
  ring

end FSInv

end

end GroundTheory.Heights₂.Heights
