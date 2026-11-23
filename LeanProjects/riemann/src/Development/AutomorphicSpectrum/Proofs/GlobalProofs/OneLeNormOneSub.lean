import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivLFunctionStrip

open Complex DirichletCharacter

namespace GlobalTheory.CompanionTheory.An

open GlobalTheory.Mem.An

theorem one_le_norm_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h1 : χ ≠ 1) {w : ℂ}
    (hw : LFunction χ w = 0) (hB : w ∉ zerosIn χ 0 1) : 1 ≤ ‖1 - w‖ := by
  have hre : w.re < 1 := by
    by_contra h
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (not_lt.1 h) hw
  by_cases h0 : 0 < w.re
  · have him : 1 < |w.im| := by
      by_contra h
      refine hB ⟨h0, hre, ?_, hw⟩
      simpa using not_lt.1 h
    have := Complex.abs_im_le_norm (1 - w)
    have e : |(1 - w).im| = |w.im| := by simp
    linarith
  · have := Complex.abs_re_le_norm (1 - w)
    have e : (1 - w).re = 1 - w.re := by simp
    rw [e] at this
    have := le_abs_self (1 - w.re)
    linarith [not_lt.1 h0]

theorem norm_sub_two_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {w : ℂ}
    (hw : w ∈ zerosIn χ 0 1) : ‖w - 2‖ ≤ 7 / 2 := by
  obtain ⟨h0, h1, h2, -⟩ := hw
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have a : (w - 2).re = w.re - 2 := by simp
  have b : (w - 2).im = w.im := by simp
  rw [a, b]
  have h3 : |w.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have h4 : |w.im| ≤ 1 := by simpa using h2
  linarith

theorem logDerOne_holds : LogDerOne := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LWide.logDeriv_LFunction_strip
  refine ⟨2 * C, fun q _ χ hq hχ => ?_⟩
  have h1 : χ ≠ 1 := by
    rintro rfl
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hχ
    omega
  have hL : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero h1
  obtain ⟨hW, hcount, hmain⟩ := H q χ h1 1 (by norm_num) (by norm_num) hL
  simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hW hcount hmain
  set W : Set ℂ := {w : ℂ | ‖w - 2‖ ≤ 7 / 2 ∧ LFunction χ w = 0} with hWdef
  set B : Set ℂ := zerosIn χ 0 1 with hBdef
  set g : ℂ → ℂ := fun w => (analyticOrderNatAt (LFunction χ) w : ℂ) / (1 - w) with hg
  have hBW : B ⊆ W := fun w hw => ⟨norm_sub_two_le hw, hw.2.2.2⟩
  have hz : zsum χ 0 1 (fun ρ => 1 / (1 - ρ)) = ∑ᶠ w ∈ B, g w := by
    unfold zsum zmult
    refine finsum_mem_congr rfl fun w _ => ?_
    simp only [hg, mul_one_div]
  have hsplit : ∑ᶠ w ∈ B, g w + ∑ᶠ w ∈ W \ B, g w = ∑ᶠ w ∈ W, g w :=
    finsum_mem_add_sdiff hBW hW
  have hD : ‖∑ᶠ w ∈ W \ B, g w‖ ≤ ∑ᶠ w ∈ W, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
    have hfin : (W \ B).Finite := hW.subset Set.diff_subset
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hW]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ w ∈ hfin.toFinset, ‖g w‖
        ≤ ∑ w ∈ hfin.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw' : w ∈ W \ B := by simpa using hw
          have h2 := one_le_norm_one_sub h1 hw'.1.2 hw'.2
          simp only [hg, norm_div, Complex.norm_natCast]
          exact div_le_self (Nat.cast_nonneg _) h2
      _ ≤ ∑ w ∈ hW.toFinset, (analyticOrderNatAt (LFunction χ) w : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
          intro x hx
          simp only [Set.Finite.mem_toFinset] at hx ⊢
          exact hx.1
  have hlog : Real.log (q * 2) ≤ Real.log (3 * q) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    exact Real.log_le_log (by positivity) (by linarith)
  rw [hz]
  have hmain' : ‖deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w‖ ≤ C * Real.log (q * 2) := hmain
  have e : deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ B, g w =
      (deriv (LFunction χ) 1 / LFunction χ 1 - ∑ᶠ w ∈ W, g w) + ∑ᶠ w ∈ W \ B, g w := by
    rw [← hsplit]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h3 := hD.trans hcount
  have h4 := mul_le_mul_of_nonneg_left hlog hC.le
  linarith

end GlobalTheory.CompanionTheory.An
