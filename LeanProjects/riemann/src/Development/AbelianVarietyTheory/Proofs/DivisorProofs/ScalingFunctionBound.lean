import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

noncomputable section

open Filter Asymptotics

namespace GlobalTheory.BigTop.Fun

theorem exists_log_le_two_rpow {eps : ℝ} (he : 0 < eps) : ∃ x0 : ℝ, ∀ y, x0 ≤ y → Real.log y ≤ 2 * y ^ eps := by
  have hev : ∀ᶠ y in atTop, Real.log y ≤ 2 * y ^ eps := by
    have h := (isLittleO_log_rpow_atTop he).bound (by norm_num : (0 : ℝ) < 2)
    filter_upwards [h, eventually_gt_atTop 0] with y hy hy0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at hy
    exact (le_abs_self _).trans hy
  exact eventually_atTop.1 hev

theorem existsIntegralMultiple : GlobalTheory.BigTop.Fun.Scale := by
  refine ⟨1, one_pos, fun eps he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := exists_log_le_two_rpow he
  refine ⟨x0, fun x hx hle i p _ => ?_⟩
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hx1 : 1 < x := Fm.one_lt_family_threshold.trans hx
  have hZx : p.Z.x = x := hsx
  have hZb : p.Z.b = Real.exp (x ^ eps) := by
    show Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) = _
    rw [hsx, hse]
  show 1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
  rw [hZx, hZb, Real.log_exp]
  have h1 : 1 ≤ x ^ eps := Real.one_le_rpow hx1.le he.le
  exact ⟨hx1.le, h1, by linarith [hx0 x hle]⟩

end GlobalTheory.BigTop.Fun

end
