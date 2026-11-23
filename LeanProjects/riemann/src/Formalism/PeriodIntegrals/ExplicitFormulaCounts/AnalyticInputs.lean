import Formalism.PeriodIntegrals.DiscIn
import Formalism.PeriodIntegrals.ZerosWindowIn
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLocal3
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth

theorem chk_discFactor : PI.DiscFactor := Formalism.ZF.zeroFactorization
theorem chk_discLog : PI.DiscLog := fun _ _ _ hf hne => Formalism.ZF.zflb_exists_log hf hne

theorem chk_zetaBoundRight : PI.ZetaBoundRight := Formalism.ZF.growthBound

theorem chk_lInvRight : PI.LInvRight := Formalism.ZeroFreeDirichlet.inverseBound

theorem chk_lBoundRight : PI.LBoundRight := by
  intro q _ χ hχ s hs
  have h := Formalism.FX.l_function_partial_sum q χ hχ ((q : ℝ) + 1)
    (fun M => Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ M) s hs 1 le_rfl
  simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, map_one, Complex.one_cpow, mul_one,
    Real.one_rpow] at h
  calc ‖DirichletCharacter.LFunction χ s‖
      = ‖(1 : ℂ) + (DirichletCharacter.LFunction χ s - 1)‖ := by congr 1; ring
    _ ≤ ‖(1 : ℂ)‖ + ‖DirichletCharacter.LFunction χ s - 1‖ := norm_add_le _ _
    _ ≤ 1 + 2 * ((q : ℝ) + 1) * (1 + ‖s‖ / s.re) := by rw [norm_one]; linarith
