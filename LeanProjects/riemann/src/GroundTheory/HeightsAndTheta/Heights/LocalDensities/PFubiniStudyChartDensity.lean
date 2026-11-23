import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsFSDensity
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP
open scoped Matrix

theorem hessC_halfLogPot_eq (N : ℕ) (z : Fin N → ℂ) :
    hessC (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z =
      (Real.pi : ℂ) • chernCoeff 0 z := by
  have h : (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) =
      fun y => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot y := rfl
  rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul', HilbertSamuel.ProjFS.hessC_logPot_eq_chernCoeff 0,
    smul_smul]
  congr 1
  push_cast
  ring

theorem FubiniStudyChartDensity.proof : FubiniStudyChartDensity.Statement := by
  intro N z w
  constructor
  · have h := ReciprocityTheory.AnForm.M.re_star_dot_hessC
      (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z (star w)
    have h' := ReciprocityTheory.AnForm.M.re_star_dot_hessC (HilbertSamuel.ProjFS.logPot (N := N)) z (star w)
    rw [star_star] at h h'
    have hl := HilbertSamuel.ProjFS.levi_logPot_nonneg z w
    have hH : hessC (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z =
        ((1 / 2 : ℝ) : ℂ) • hessC (HilbertSamuel.ProjFS.logPot (N := N)) z :=
      ReciprocityTheory.AnForm.M.hessC_const_mul' (1 / 2) HilbertSamuel.ProjFS.logPot z
    rw [← h, hH, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, h']
    positivity
  · unfold maDens
    rw [ReciprocityTheory.AnForm.A.mdisc_const, hessC_halfLogPot_eq, Matrix.det_smul, Fintype.card_fin,
      det_chernCoeff, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hS := one_add_normSqSum_pos z
    have hpi := Real.pi_pos
    change (N.factorial : ℝ) * (2 / Real.pi) ^ N *
        (Real.pi ^ N * ((1 / (2 * Real.pi)) ^ N / (1 + normSqSum z) ^ (N + 1))) = _
    rw [div_pow, div_pow, one_pow, mul_pow]
    field_simp
    rfl

end GroundTheory.Heights₂.Heights.FourB
