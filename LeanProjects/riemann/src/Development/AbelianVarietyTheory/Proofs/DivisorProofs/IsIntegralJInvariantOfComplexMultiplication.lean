import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModVanish
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.JInt

theorem not_four_sq {u Δ : ℤ} (hu : Δ ≤ u) (hΔ : 0 < Δ) (r : ℤ) : u ^ 2 + Δ ≠ 4 * (r * r) := by
  intro h
  have h2 : (2 * |r|) ^ 2 = u ^ 2 + Δ := by rw [mul_pow, sq_abs]; linarith
  have hr0 : 0 ≤ 2 * |r| := by positivity
  have hu0 : 0 ≤ u := by linarith
  have a1 : u < 2 * |r| := by nlinarith
  have a2 : 2 * |r| < u + 1 := by nlinarith
  omega

theorem disc_pos {A B C D : ℤ} {τ : ℍ} (hC : C ≠ 0)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : 0 < -((D - A) ^ 2 + 4 * B * C) := by
  set x := (τ : ℂ).re
  set y := (τ : ℂ).im
  have hy : 0 < y := τ.im_pos
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im] at hre him
  have h1 : ((D : ℝ) - A + 2 * C * x) * y = 0 := by linear_combination -him
  have h1' : (D : ℝ) - A + 2 * C * x = 0 := (mul_eq_zero.mp h1).resolve_right hy.ne'
  have key : (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) = 4 * (C : ℝ) ^ 2 * y ^ 2 := by
    push_cast
    linear_combination (-(D : ℝ) + A - 2 * C * x) * h1' - 4 * (C : ℝ) * hre
  have hCr : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
  have : (0 : ℝ) < (((-((D - A) ^ 2 + 4 * B * C)) : ℤ) : ℝ) := by rw [key]; positivity
  exact_mod_cast this

theorem main : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ) (α : ℂ), IsTauOf L c τ → MulStable L α → α.im ≠ 0 →
    IsIntegral ℤ (jT τ) := by
  intro L c τ α hτ hα him
  obtain ⟨hc, hlat⟩ := hτ
  have h1 : c * (τ : ℂ) ∈ L.lattice := (hlat _).2 ⟨1, 0, by simp⟩
  have h2 : c ∈ L.lattice := (hlat _).2 ⟨0, 1, by simp⟩
  obtain ⟨A, B, hAB⟩ := (hlat _).1 (hα _ h1)
  obtain ⟨C, D, hCD⟩ := (hlat _).1 (hα _ h2)
  have e1 : α * (τ : ℂ) = A * τ + B := by apply mul_left_cancel₀ hc; linear_combination hAB
  have e2 : α = C * τ + D := by apply mul_left_cancel₀ hc; linear_combination hCD
  have hfix : (A : ℂ) * τ + B = τ * (C * τ + D) := by rw [← e1, e2]; ring
  have hC : C ≠ 0 := by
    rintro rfl
    apply him; rw [e2]; simp
  have hΔ := disc_pos hC hfix
  set Δ := -((D - A) ^ 2 + 4 * B * C) with hΔdef
  set t := A + D
  set k := Δ + |t|
  set M := (A + k) * (D + k) - B * C with hM
  have h4M : 4 * M = (2 * k + t) ^ 2 + Δ := by rw [hM, hΔdef]; ring
  have hu : Δ ≤ 2 * k + t := by
    have := neg_abs_le t; have := abs_nonneg t; linarith
  have hMpos : 0 < M := by nlinarith
  have hm : 0 < M.toNat := by omega
  have hMc : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hMpos.le
  refine jT_isIntegral hm ?_ (Gm_vanish hm τ (A + k) B C (D + k) (by rw [hMc]) ?_)
  · rintro ⟨r, hr⟩
    have : M = (r : ℤ) * r := by rw [← hMc, hr]; push_cast; ring
    exact not_four_sq hu hΔ r (by rw [← h4M, this])
  · push_cast; linear_combination hfix

end GlobalTheory.JInt
