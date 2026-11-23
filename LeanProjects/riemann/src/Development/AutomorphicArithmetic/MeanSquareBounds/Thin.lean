import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Development.AutomorphicArithmetic.MeanSquareBounds.GIntegral
import Development.AutomorphicArithmetic.MeanSquareBounds.PsiThin
import Development.AutomorphicArithmetic.MeanSquareBounds.IntThin

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem thin :
    ∀ ε A c c₀ : ℝ, 0 < ε → 0 < A → 0 < c → 0 < c₀ → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      Real.log N ≤ A * x ^ (ε / 5) * Real.log x ^ 2 → (χ ^ 2 = 1 → χ ≠ 1 → NoExc c₀ χ) →
      ∀ y : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → ‖G0 χ y‖ ≤ y * Real.exp (-(c * x ^ (ε / 8))) := by
  intro ε A c c₀ hε hA hc hc₀
  obtain ⟨C, c1, hC, hc1, hpsi⟩ := psi_thin c₀ hc₀
  obtain ⟨x1, hx1⟩ := int_thin ε c1 C (A + 1) c hε hc1 hC (by linarith) hc
  refine ⟨max x1 (max (Real.exp 1) ((3 : ℝ) ^ (3 / ε))), ?_⟩
  intro x hx N _ χ hprim hN hexc y hy
  have hx1' : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : (3 : ℝ) ^ (3 / ε) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hxone : 1 ≤ x := he1.trans hxe
  have hpow3 : (3 : ℝ) ≤ x ^ (ε / 3) := by
    calc (3 : ℝ) = ((3 : ℝ) ^ (3 / ε)) ^ (ε / 3) := by
          rw [← Real.rpow_mul (by norm_num)]
          have : 3 / ε * (ε / 3) = 1 := by field_simp
          rw [this, Real.rpow_one]
      _ ≤ x ^ (ε / 3) := Real.rpow_le_rpow (by positivity) hx3 (by positivity)
  have hy1 : Real.exp 1 ≤ y := by
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h3 : Real.exp 3 = Real.exp 1 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    have h4 : Real.exp 3 ≤ Real.exp (x ^ (ε / 3)) := Real.exp_le_exp.2 hpow3
    have h5 : Real.exp 1 * 3 ≤ Real.exp 3 := by rw [h3]; nlinarith [Real.exp_pos 1]
    linarith
  have hy1' : 1 ≤ y := he1.trans hy1
  have hlogx : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at this
  have hxε : 1 ≤ x ^ (ε / 5) := Real.one_le_rpow hxone (by positivity)
  have hP : 1 ≤ x ^ (ε / 5) * Real.log x ^ 2 := one_le_mul_of_one_le_of_one_le hxε (one_le_pow₀ hlogx)
  have hlam : max 1 (Real.log N) ≤ (A + 1) * x ^ (ε / 5) * Real.log x ^ 2 := by
    rw [mul_assoc]
    rw [mul_assoc] at hN
    refine max_le (by nlinarith) (by nlinarith)
  have hψ := hpsi N χ (max 1 (Real.log N)) hprim (le_max_left _ _) (le_max_right _ _) hexc
  rw [g_integral N χ hprim y hy1', neg_mul, norm_neg]
  exact hx1 x hx1' y (max 1 (Real.log N)) (PI.psi0 χ) hy (le_max_left _ _) hlam
    (fun u hu => hψ u (hy1.trans hu))

end QH
