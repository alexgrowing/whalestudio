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

namespace GlobalTheory.CompanionTheory.PerUC.GxLe

theorem one_var_small (s : ℝ) (hs0 : 0 < s) (r Y : ℝ) (N : ℕ) (hr : 0 < r) (hr1 : r ≤ 1)
    (h1 : r ^ 2 / 4 ≤ Y) (h2 : Y ≤ r ^ 2) :
    r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N) ≤ (51 + 2 / s) * min (r ^ s) (r⁻¹ ^ s) := by
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hp : 0 < r ^ s := Real.rpow_pos_of_pos hr _
  have hp1 : r ^ s ≤ 1 := Real.rpow_le_one hr.le hr1 hs0.le
  have hq : r⁻¹ ^ s * r ^ s = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.2 hr.le) hr.le, inv_mul_cancel₀ hr.ne', Real.one_rpow]
  have hq1 : 1 ≤ r⁻¹ ^ s := Real.one_le_rpow ((one_le_inv₀ hr).2 hr1) hs0.le
  have hmin : min (r ^ s) (r⁻¹ ^ s) = r ^ s := min_eq_left (hp1.trans hq1)
  have hlog4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]
    have := Real.log_two_lt_d9
    linarith
  have hlogY : Real.log Y ≤ 0 := Real.log_nonpos hY.le (h2.trans (by nlinarith))
  have hlogr : Real.log (r ^ 2 / 4) ≤ Real.log Y := Real.log_le_log (by positivity) h1
  have hexp : Real.log (r ^ 2 / 4) = 2 * Real.log r - Real.log 4 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; norm_num
  have habs : |Real.log Y| ≤ Real.log 4 + 2 * Real.log r⁻¹ := by
    rw [abs_of_nonpos hlogY, Real.log_inv]; linarith
  have hl : Real.log r⁻¹ ≤ r⁻¹ ^ s / s := Real.log_le_rpow_div (inv_nonneg.2 hr.le) hs0
  have hW : 1 ≤ (1 + Y) ^ N := one_le_pow₀ (by linarith)
  have hL0 : 0 ≤ 1 + |Real.log Y| := by positivity
  have hfrac : (1 + |Real.log Y|) / (1 + Y) ^ N ≤ 1 + |Real.log Y| := div_le_self hL0 hW
  have hkey : r ^ s * (1 + |Real.log Y|) ≤ 51 + 2 / s := by
    have e1 : r ^ s * (1 + |Real.log Y|) ≤ r ^ s * (3 + 2 * (r⁻¹ ^ s / s)) := by
      apply mul_le_mul_of_nonneg_left _ hp.le
      linarith
    have e2 : r ^ s * (3 + 2 * (r⁻¹ ^ s / s)) = 3 * r ^ s + 2 / s := by
      have : r ^ s * (2 * (r⁻¹ ^ s / s)) = 2 / s * (r⁻¹ ^ s * r ^ s) := by ring
      rw [mul_add, this, hq]; ring
    linarith
  rw [hmin, show r ^ (2 * s) = r ^ s * r ^ s by rw [two_mul, Real.rpow_add hr]]
  calc r ^ s * r ^ s * ((1 + |Real.log Y|) / (1 + Y) ^ N)
      ≤ r ^ s * r ^ s * (1 + |Real.log Y|) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = (r ^ s * (1 + |Real.log Y|)) * r ^ s := by ring
    _ ≤ (51 + 2 / s) * r ^ s := mul_le_mul_of_nonneg_right hkey hp.le

theorem one_var_large (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (r Y : ℝ) (N : ℕ) (hN : 3 ≤ N)
    (hr1 : 1 ≤ r) (h1 : r ^ 2 / 4 ≤ Y) (h2 : Y ≤ r ^ 2) :
    r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N) ≤ (51 + 2 / s) * min (r ^ s) (r⁻¹ ^ s) := by
  have hr : 0 < r := by linarith
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hp : 0 < r ^ s := Real.rpow_pos_of_pos hr _
  have hq0 : 0 < r⁻¹ ^ s := Real.rpow_pos_of_pos (inv_pos.2 hr) _
  have hq : r⁻¹ ^ s * r ^ s = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.2 hr.le) hr.le, inv_mul_cancel₀ hr.ne', Real.one_rpow]
  have hq1 : r⁻¹ ^ s ≤ 1 :=
    Real.rpow_le_one (inv_nonneg.2 hr.le) (inv_le_one_of_one_le₀ hr1) hs0.le
  have hp1 : 1 ≤ r ^ s := Real.one_le_rpow hr1 hs0.le
  have hmin : min (r ^ s) (r⁻¹ ^ s) = r⁻¹ ^ s := min_eq_right (hq1.trans hp1)
  have hlog4 : Real.log 4 ≤ 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]
    have := Real.log_two_lt_d9
    linarith
  have hW1 : 1 ≤ 1 + Y := by linarith
  have hW0 : 0 < 1 + Y := by linarith
  have hL : 1 + |Real.log Y| ≤ 3 * (1 + Y) := by
    by_cases hY1 : 1 ≤ Y
    · rw [abs_of_nonneg (Real.log_nonneg hY1)]
      have := Real.log_le_sub_one_of_pos hY
      linarith
    · have hY2 : Y ≤ 1 := (not_le.1 hY1).le
      rw [abs_of_nonpos (Real.log_nonpos hY.le hY2)]
      have hq4 : (4 : ℝ)⁻¹ ≤ Y := by nlinarith
      have := Real.log_le_log (by norm_num) hq4
      rw [Real.log_inv] at this
      linarith
  have hr3 : r ^ (3 * s) ≤ 16 * (1 + Y) ^ 2 := by
    have a1 : r ^ (3 * s) ≤ r ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
    have a2 : r ^ (3 : ℝ) = r ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have a3 : r ^ 2 ≤ 4 * (1 + Y) := by linarith
    have a4 : r ^ 3 ≤ r ^ 2 * r ^ 2 := by nlinarith [sq_nonneg r, mul_nonneg (sq_nonneg r) (sub_nonneg.2 hr1), mul_nonneg (mul_nonneg (sq_nonneg r) hr.le) (sub_nonneg.2 hr1)]
    have a5 : r ^ 2 * r ^ 2 ≤ (4 * (1 + Y)) * (4 * (1 + Y)) :=
      mul_le_mul a3 a3 (by positivity) (by positivity)
    rw [a2] at a1
    calc r ^ (3 * s) ≤ r ^ 3 := a1
      _ ≤ r ^ 2 * r ^ 2 := a4
      _ ≤ (4 * (1 + Y)) * (4 * (1 + Y)) := a5
      _ = 16 * (1 + Y) ^ 2 := by ring
  have hWN : (1 + Y) ^ 3 ≤ (1 + Y) ^ N := pow_le_pow_right₀ hW1 hN
  have hmain : r ^ (3 * s) * (1 + |Real.log Y|) ≤ 48 * (1 + Y) ^ N := by
    calc r ^ (3 * s) * (1 + |Real.log Y|) ≤ 16 * (1 + Y) ^ 2 * (3 * (1 + Y)) :=
          mul_le_mul hr3 hL (by positivity) (by positivity)
      _ = 48 * (1 + Y) ^ 3 := by ring
      _ ≤ 48 * (1 + Y) ^ N := by linarith
  have h3 : r ^ (3 * s) = r ^ (2 * s) * r ^ s := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hWp : 0 < (1 + Y) ^ N := by positivity
  rw [hmin]
  have hs2 : 0 < 2 / s := by positivity
  calc r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N)
      = (r ^ (2 * s) * (r⁻¹ ^ s * r ^ s)) * ((1 + |Real.log Y|) / (1 + Y) ^ N) := by
        rw [hq, mul_one]
    _ = (r ^ (3 * s) * (1 + |Real.log Y|) / (1 + Y) ^ N) * r⁻¹ ^ s := by rw [h3]; ring
    _ ≤ 48 * r⁻¹ ^ s :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ hWp).2 hmain) hq0.le
    _ ≤ (51 + 2 / s) * r⁻¹ ^ s := mul_le_mul_of_nonneg_right (by linarith) hq0.le

theorem one_var (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (r Y : ℝ) (N : ℕ) (hN : 3 ≤ N)
    (hr : 0 < r) (h1 : r ^ 2 / 4 ≤ Y) (h2 : Y ≤ r ^ 2) :
    r ^ (2 * s) * ((1 + |Real.log Y|) / (1 + Y) ^ N) ≤ (51 + 2 / s) * min (r ^ s) (r⁻¹ ^ s) := by
  rcases le_total r 1 with hr1 | hr1
  · exact one_var_small s hs0 r Y N hr hr1 h1 h2
  · exact one_var_large s hs0 hs1 r Y N hN hr1 h1 h2

theorem alg_id (a Z P Q L IA IB : ℝ) (ha : a ≠ 0) (hZ : Z ≠ 0) (hP : P ≠ 0) :
    ((a * Z) ^ 3)⁻¹ * (Z / a) * L * Q * (IA * IB) =
      ((a ^ 4)⁻¹ * P) * IA * IB * (Z ^ 2)⁻¹ * (Q / P * L) := by
  field_simp

theorem real_step (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (a Z R A B H : ℝ) (N : ℕ) (hN : 3 ≤ N)
    (ha : 0 < a) (hZ : 0 < Z) (hR1 : a ^ 2 ≤ R) (hR2 : R ≤ 2 * a ^ 2)
    (hA : 0 < A) (hB : 0 < B) (hHnn : 0 ≤ H⁻¹) (hH : H⁻¹ ≤ A⁻¹ * B⁻¹) :
    ((a * Z) ^ 3)⁻¹ * (((a * Z) ^ 2 / R ^ 2) ^ ((1 : ℝ) / 2) *
        (1 + |Real.log ((a * Z) ^ 2 / R ^ 2)|) / (1 + (a * Z) ^ 2 / R ^ 2) ^ N) *
      (a / (a * Z)) ^ (2 * σ - 2) / H ≤
    (51 + 2 / (1 - σ)) * (a ^ (-2 - 2 * σ) * A⁻¹ * B⁻¹ *
      ((Z ^ 2)⁻¹ * min ((Z / a) ^ (1 - σ)) ((a / Z) ^ (1 - σ)))) := by
  have hs0 : 0 < 1 - σ := by linarith
  have hs1 : 1 - σ ≤ 1 := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR1
  have hr : 0 < Z / a := div_pos hZ ha
  have hYsq : (a * Z) ^ 2 / R ^ 2 = (a * Z / R) ^ 2 := by rw [div_pow]
  have hT : ((a * Z) ^ 2 / R ^ 2) ^ ((1 : ℝ) / 2) = a * Z / R := by
    rw [hYsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  have hT2 : a * Z / R ≤ Z / a := by
    rw [div_le_div_iff₀ hR0 ha]
    nlinarith [mul_le_mul_of_nonneg_left hR1 hZ.le]
  have hT1 : Z / a / 2 ≤ a * Z / R := by
    rw [div_div, div_le_div_iff₀ (by positivity) hR0]
    nlinarith [mul_le_mul_of_nonneg_left hR2 hZ.le]
  have hY2 : (a * Z) ^ 2 / R ^ 2 ≤ (Z / a) ^ 2 := by
    rw [hYsq]
    exact pow_le_pow_left₀ (by positivity) hT2 2
  have hY1 : (Z / a) ^ 2 / 4 ≤ (a * Z) ^ 2 / R ^ 2 := by
    rw [hYsq]
    calc (Z / a) ^ 2 / 4 = (Z / a / 2) ^ 2 := by ring
      _ ≤ (a * Z / R) ^ 2 := pow_le_pow_left₀ (by positivity) hT1 2
  have hone := one_var (1 - σ) hs0 hs1 (Z / a) ((a * Z) ^ 2 / R ^ 2) N hN hr hY1 hY2
  rw [inv_div] at hone
  have hcol : (a / (a * Z)) ^ (2 * σ - 2) = Z ^ (2 * (1 - σ)) := by
    have : a / (a * Z) = Z⁻¹ := by field_simp
    rw [this, Real.inv_rpow hZ.le, ← Real.rpow_neg hZ.le]
    congr 1
    ring
  have hrp : (Z / a) ^ (2 * (1 - σ)) = Z ^ (2 * (1 - σ)) / a ^ (2 * (1 - σ)) :=
    Real.div_rpow hZ.le ha.le _
  have hap : a ^ (-2 - 2 * σ) = (a ^ 4)⁻¹ * a ^ (2 * (1 - σ)) := by
    have e : (-2 - 2 * σ : ℝ) = -((4 : ℕ) : ℝ) + 2 * (1 - σ) := by push_cast; ring
    rw [e, Real.rpow_add ha, Real.rpow_neg ha.le, Real.rpow_natCast]
  rw [hT, hcol, hap]
  rw [hrp] at hone
  have hP : 0 < a ^ (2 * (1 - σ)) := Real.rpow_pos_of_pos ha _
  have hQ : 0 < Z ^ (2 * (1 - σ)) := Real.rpow_pos_of_pos hZ _
  generalize a ^ (2 * (1 - σ)) = P at *
  generalize Z ^ (2 * (1 - σ)) = Q at *
  generalize hLdef : (1 + |Real.log ((a * Z) ^ 2 / R ^ 2)|) / (1 + (a * Z) ^ 2 / R ^ 2) ^ N = L at *
  have hL0 : 0 ≤ L := by
    rw [← hLdef]
    positivity
  have e1 : ((a * Z) ^ 3)⁻¹ * (a * Z / R * (1 + |Real.log ((a * Z) ^ 2 / R ^ 2)|) /
        (1 + (a * Z) ^ 2 / R ^ 2) ^ N) * Q / H = ((a * Z) ^ 3)⁻¹ * (a * Z / R) * L * Q * H⁻¹ := by
    rw [← hLdef]
    ring
  have hfac : 0 ≤ ((a ^ 4)⁻¹ * P) * A⁻¹ * B⁻¹ * (Z ^ 2)⁻¹ := by positivity
  rw [e1]
  calc ((a * Z) ^ 3)⁻¹ * (a * Z / R) * L * Q * H⁻¹
      ≤ ((a * Z) ^ 3)⁻¹ * (Z / a) * L * Q * (A⁻¹ * B⁻¹) := by
        have : ((a * Z) ^ 3)⁻¹ * (a * Z / R) * L * Q ≤ ((a * Z) ^ 3)⁻¹ * (Z / a) * L * Q := by
          gcongr
        exact mul_le_mul this hH (hHnn) (by positivity)
    _ = ((a ^ 4)⁻¹ * P) * A⁻¹ * B⁻¹ * (Z ^ 2)⁻¹ * (Q / P * L) :=
        alg_id a Z P Q L A⁻¹ B⁻¹ ha.ne' hZ.ne' hP.ne'
    _ ≤ ((a ^ 4)⁻¹ * P) * A⁻¹ * B⁻¹ * (Z ^ 2)⁻¹ *
          ((51 + 2 / (1 - σ)) * min ((Z / a) ^ (1 - σ)) ((a / Z) ^ (1 - σ))) :=
        mul_le_mul_of_nonneg_left hone hfac
    _ = _ := by ring

open GlobalTheory.CompanionTheory.MajC in

theorem gx_le_ga : ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀, ∀ h : Ad3.K.LC.M22,
    ‖h 1 0‖ ≤ ‖h 0 0‖ → GlobalTheory.CompanionTheory.MajC.dt h ≠ 0 →
    GlobalTheory.CompanionTheory.PerUC.gx σ N h ≤ C * GlobalTheory.CompanionTheory.PerUC.ga σ 4 h := by
  intro σ hσ0 hσ1
  refine ⟨51 + 2 / (1 - σ), 8, fun N hN h hv hd => ?_⟩
  have hu : h 0 0 ≠ 0 := by
    intro hu
    have hv0 : h 1 0 = 0 := by
      rw [hu, norm_zero] at hv
      exact norm_le_zero_iff.1 hv
    apply hd
    rw [dt_eq, hu, hv0]
    simp
  have hga : GlobalTheory.CompanionTheory.PerUC.ga σ 4 h = ‖h 0 0‖ ^ (-2 - 2 * σ) * ((1 + ‖h 0 0‖) ^ 4)⁻¹ *
      ((1 + ‖h 0 1‖) ^ 4)⁻¹ * kern (1 - σ) ‖h 0 0‖ (h 1 1 - h 1 0 / h 0 0 * h 0 1) := by
    unfold GlobalTheory.CompanionTheory.PerUC.ga
    rw [if_pos ⟨hv, hu⟩]
  rw [hga]
  set z := h 1 1 - h 1 0 / h 0 0 * h 0 1 with hz
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = h 0 0 * z := by
    rw [hz]; field_simp
  have hU : 0 < ‖h 0 0‖ := norm_pos_iff.2 hu
  have hdt : dt h = ‖h 0 0‖ * ‖z‖ := by rw [dt_eq, hdet, norm_mul]
  have hZ : 0 < ‖z‖ := by
    have : 0 < dt h := lt_of_le_of_ne (by rw [dt_eq]; exact norm_nonneg _) (Ne.symm hd)
    rw [hdt] at this
    exact (pos_iff_pos_of_mul_pos this).1 hU
  have hcol : GlobalTheory.CompanionTheory.MajC.col h = ‖h 0 0‖ := max_eq_left hv
  have hk : kern (1 - σ) ‖h 0 0‖ z = (‖z‖ ^ 2)⁻¹ *
      min ((‖z‖ / ‖h 0 0‖) ^ (1 - σ)) ((‖h 0 0‖ / ‖z‖) ^ (1 - σ)) := rfl
  have hA : ((1 + ‖h‖) ^ N)⁻¹ ≤ ((1 + ‖h 0 0‖) ^ 4)⁻¹ * ((1 + ‖h 0 1‖) ^ 4)⁻¹ := by
    rw [← mul_inv]
    apply inv_anti₀ (by positivity)
    have h1 : 1 + ‖h 0 0‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 0]
    have h2 : 1 + ‖h 0 1‖ ≤ 1 + ‖h‖ := by linarith [entry_le h 0 1]
    have h3 : (1 : ℝ) ≤ 1 + ‖h‖ := by linarith [norm_nonneg h]
    calc (1 + ‖h 0 0‖) ^ 4 * (1 + ‖h 0 1‖) ^ 4
        ≤ (1 + ‖h‖) ^ 4 * (1 + ‖h‖) ^ 4 := by gcongr
      _ = (1 + ‖h‖) ^ 8 := by ring
      _ ≤ (1 + ‖h‖) ^ N := pow_le_pow_right₀ h3 hN
  have hgx : GlobalTheory.CompanionTheory.PerUC.gx σ N h = (dt h ^ 3)⁻¹ *
      ((dt h ^ 2 / GlobalTheory.CompanionTheory.PerUC.rr h ^ 2) ^ ((1 : ℝ) / 2) *
        (1 + |Real.log (dt h ^ 2 / GlobalTheory.CompanionTheory.PerUC.rr h ^ 2)|) /
        (1 + dt h ^ 2 / GlobalTheory.CompanionTheory.PerUC.rr h ^ 2) ^ N) *
      (GlobalTheory.CompanionTheory.MajC.col h / dt h) ^ (2 * σ - 2) / (1 + ‖h‖) ^ N := rfl
  have hR1 : ‖h 0 0‖ ^ 2 ≤ GlobalTheory.CompanionTheory.PerUC.rr h := by
    unfold GlobalTheory.CompanionTheory.PerUC.rr
    nlinarith [sq_nonneg ‖h 1 0‖]
  have hR2 : GlobalTheory.CompanionTheory.PerUC.rr h ≤ 2 * ‖h 0 0‖ ^ 2 := by
    unfold GlobalTheory.CompanionTheory.PerUC.rr
    nlinarith [norm_nonneg (h 1 0)]
  rw [hgx, hk, hdt, hcol]
  exact real_step σ hσ0 hσ1 ‖h 0 0‖ ‖z‖ _ _ _ _ N (by omega) hU hZ hR1 hR2
    (by positivity) (by positivity) (by positivity) hA

end GlobalTheory.CompanionTheory.PerUC.GxLe
