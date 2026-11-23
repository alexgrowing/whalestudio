import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel

noncomputable section

open NumberField

namespace GlobalTheory.FrameDegSize

theorem third_le_log_rootDiscr {E : Type} [Field E] [NumberField E] (h : 1 < Module.finrank ℚ E) :
    (1 : ℝ) / 3 ≤ Real.log (rootDiscr E) := by
  set n := Module.finrank ℚ E with hn
  have hπ := Real.pi_gt_three
  have h1 := abs_discr_ge h
  rw [← hn] at h1
  have hn2 : 2 ≤ n := h
  have hpow : (9 / 4 : ℝ) ≤ (Real.pi / 2) ^ n :=
    calc (9 / 4 : ℝ) ≤ (Real.pi / 2) ^ 2 := by nlinarith
      _ ≤ (Real.pi / 2) ^ n := pow_le_pow_right₀ (by linarith) hn2
  have hsplit : (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ n = (4 / 9 * (Real.pi / 2) ^ n) * (3 / 2) ^ n := by
    rw [mul_assoc, ← mul_pow]; congr 2; ring
  have h2 : ((3 : ℝ) / 2) ^ n ≤ ((|discr E| : ℤ) : ℝ) := by
    refine le_trans ?_ (hsplit ▸ h1)
    have h0 : (0 : ℝ) ≤ (3 / 2) ^ n := by positivity
    have : (1 : ℝ) ≤ 4 / 9 * (Real.pi / 2) ^ n := by linarith
    nlinarith
  have hd : (0 : ℝ) < ((|discr E| : ℤ) : ℝ) := lt_of_lt_of_le (by positivity) h2
  unfold rootDiscr
  rw [← hn, Real.log_rpow hd]
  have h3 : (n : ℝ) * Real.log (3 / 2) ≤ Real.log ((|discr E| : ℤ) : ℝ) := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2
  have h4 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 3 / 2) (by norm_num)
    norm_num at this ⊢; linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [inv_mul_eq_div, le_div_iff₀ hnpos]
  nlinarith

theorem gamma_add_log_two_pi_le : Real.eulerMascheroniConstant + Real.log (2 * Real.pi) ≤ 4 := by
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  rw [Real.log_mul (by norm_num) hπ0.ne']
  have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h3 : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos hπ0
  linarith

theorem abs_re_logOm_le {E : Type} [Field E] [NumberField E] (h : 1 < Module.finrank ℚ E) {d : ℕ} [NeZero d]
    (χ : DirichletCharacter ℂ d) :
    |(GlobalTheory.CM.logOm E χ).re| ≤ 13 * Real.log (rootDiscr E) + |(deriv χ.LFunction 1 / χ.LFunction 1).re| := by
  have hl := third_le_log_rootDiscr h
  have hg := gamma_add_log_two_pi_le
  have hγ : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have hlp : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hrd : 0 < rootDiscr E := by
    rcases (show (0 : ℝ) ≤ rootDiscr E by unfold rootDiscr; positivity).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, Real.log_zero] at hl; linarith
  have e : (GlobalTheory.CM.logOm E χ).re = Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log (rootDiscr E) -
      (deriv χ.LFunction 1 / χ.LFunction 1).re := by
    unfold GlobalTheory.CM.logOm
    rw [Complex.sub_re, Complex.ofReal_re, Real.log_div (by positivity) hrd.ne']
    ring
  rw [e]
  have ha := abs_nonneg (deriv χ.LFunction 1 / χ.LFunction 1).re
  have h1 := le_abs_self (deriv χ.LFunction 1 / χ.LFunction 1).re
  have h2 := neg_abs_le (deriv χ.LFunction 1 / χ.LFunction 1).re
  rw [abs_le]; constructor <;> nlinarith

theorem rootDiscr_host (D : Formalism.BasicNotions.D7) : rootDiscr D.host.E = D.host.rdE := by
  unfold rootDiscr Formalism.BasicNotions.Host.rdE
  rw [Int.cast_abs, one_div]

theorem one_lt_finrank_host (D : Formalism.BasicNotions.D7) : 1 < Module.finrank ℚ D.host.E := by
  rw [D.host.finrank_cmField]
  have := D.R.ord_pos
  omega

theorem abs_half_sub_mul_logOm_le (D : Formalism.BasicNotions.D7) (p q : ℕ) :
    haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
    |((p : ℝ) - q) / 2 * (GlobalTheory.CM.logOm D.host.E (Formalism.BasicNotions.chiK D)).re| ≤
      7 * ((p : ℝ) + q) * (Real.log D.host.rdE + |Formalism.BasicNotions.dlogL D 1|) := by
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have h := abs_re_logOm_le (one_lt_finrank_host D) (Formalism.BasicNotions.chiK D)
  rw [rootDiscr_host] at h
  have hl := third_le_log_rootDiscr (one_lt_finrank_host D)
  rw [rootDiscr_host] at hl
  have hdl : (deriv (Formalism.BasicNotions.chiK D).LFunction 1 / (Formalism.BasicNotions.chiK D).LFunction 1).re = Formalism.BasicNotions.dlogL D 1 := rfl
  rw [hdl] at h
  have hpq : |((p : ℝ) - q) / 2| ≤ ((p : ℝ) + q) / 2 := by
    rw [abs_div, abs_two]
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have : |(p : ℝ) - q| ≤ p + q := by rw [abs_le]; constructor <;> linarith
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hs : (0 : ℝ) ≤ (p : ℝ) + q := by positivity
  have ha := abs_nonneg (Formalism.BasicNotions.dlogL D 1)
  rw [abs_mul]
  calc |((p : ℝ) - q) / 2| * |(GlobalTheory.CM.logOm D.host.E (Formalism.BasicNotions.chiK D)).re|
      ≤ ((p : ℝ) + q) / 2 * (13 * Real.log D.host.rdE + |Formalism.BasicNotions.dlogL D 1|) :=
        mul_le_mul hpq h (abs_nonneg _) (by positivity)
    _ ≤ 7 * ((p : ℝ) + q) * (Real.log D.host.rdE + |Formalism.BasicNotions.dlogL D 1|) := by nlinarith

end GlobalTheory.FrameDegSize

end
