import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.SharpRestriction.ElevenLe

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV

theorem logDerivative_and_regulator_bound (D : D7) (L : SizeData₂ D) (hdl : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps)
    (hrd : 1 ≤ D.host.rdE) (hx : 16 ≤ L.sc.x) :
    LocalQuadraticParts.adm23 L := by
  have : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  refine ⟨⟨chiK D, ?_, ?_⟩, ?_⟩
  · intro n
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    simp [chiK, MulChar.ringHomComp_apply, legendreSym]
  · have him := GlobalTheoryTheory.log_deriv_L_one_real_im_eq_zero (chiK D) (GlobalTheoryTheory.jnt_chiK_ne_one D) (GlobalTheoryTheory.jnt_chiK_real D)
    rw [L.logDerivative_at_one_eq]
    apply Complex.ext
    · simp [dlogL]
    · simpa [GlobalTheoryTheory.logDerivativeAtOne] using him.symm
  · have hx0 : 0 < L.sc.x := by linarith
    have hv : D.host.v = D.host.rdE / 2 := rfl
    have hrd0 : 0 < D.host.rdE := by linarith
    have hlrd : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hrd
    have h1 : Real.log (Real.pi / D.host.v) = Real.log (2 * Real.pi) - Real.log D.host.rdE := by
      rw [hv, ← Real.log_div (by positivity) hrd0.ne']
      congr 1
      field_simp
    have h2 : Real.log (2 * Real.pi) ≤ 3 * Real.log 2 := by
      have : Real.log (2 * Real.pi) ≤ Real.log ((2 : ℝ) ^ 3) :=
        Real.log_le_log (by positivity) (by nlinarith [Real.pi_le_four])
      rwa [Real.log_pow] at this
    have h2' : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have h3 : 4 * Real.log 2 ≤ Real.log L.sc.x := by
      have : Real.log ((2 : ℝ) ^ 4) ≤ Real.log L.sc.x := Real.log_le_log (by positivity) (by linarith)
      rwa [Real.log_pow] at this
    have h4 : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
      unfold SizeData₂.La Scale.a Scale.b
      rw [Real.log_mul (by positivity) hrd0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have h5 : |L.logDerivativeAtOne| ≤ L.sc.L := hdl
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have hg0 : 0 < Real.eulerMascheroniConstant := by
      have := Real.one_half_lt_eulerMascheroniConstant; linarith
    have hl2 := Real.log_two_gt_d9
    obtain ⟨h5a, h5b⟩ := abs_le.mp h5
    unfold SizeData₂.logOm
    rw [h1, h4, abs_le]
    constructor <;> linarith

theorem family_logDerivative_regulator_bound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps ∧ 1 ≤ (Fm.D x i).host.rdE) :
    LocalQuadraticParts.PeriodFamily' Fm := by
  obtain ⟨xE, hE⟩ := hE
  refine ⟨max xE (max 16 (Fm.x1 + 1)), fun x hx i => ?_⟩
  have hxE : xE ≤ x := le_trans (le_max_left _ _) hx
  have hx16 : 16 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x :=
    lt_of_lt_of_le (by linarith) (le_trans (le_trans (le_max_right 16 _) (le_max_right _ _)) hx)
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  exact logDerivative_and_regulator_bound _ _ (hE x hxE i).1 (hE x hxE i).2 (by rw [hsx]; exact hx16)

end Formalism.MainNotions.J
