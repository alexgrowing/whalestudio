import Mathlib
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

namespace Formalism.EigenvalueLevelCeiling

theorem depth_cases : DepthCases := by
  unfold DepthCases
  intro e ec F
  refine ⟨fun a h1 h2 => by linarith, fun h1 h2 h3 => by linarith,
    fun s T β h1 h2 h3 h4 => by linarith, fun s T h1 h2 h3 => by linarith,
    fun T nn nnc g2 h1 h2 h3 => by linarith⟩

theorem unipotent_numeric : UnipNum := by
  unfold UnipNum
  intro f r d dK δq hf hr hd hq
  have hr0 : 0 ≤ r - 1 := by linarith
  have hA : 0 ≤ f * r * (r - 1) / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hf (by linarith)) hr0) (by norm_num)
  have h1 : f * r * (r - 1) / 2 * (d + dK / δq) ≤ f * r * (r - 1) / 2 * (4 * d) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have h2 : 0 ≤ f * r * d := mul_nonneg (mul_nonneg hf (by linarith)) hd
  have h3 : f * r * (r - 1) / 2 * (4 * d) = 2 * f * r ^ 2 * d - 2 * (f * r * d) := by ring
  linarith

theorem budget_numeric : BudgetNum := by
  unfold BudgetNum
  intro dK δq D B hδ hD hB hq
  rw [div_le_iff₀ (mul_pos hδ hD)]
  have h1 : dK ≤ 3 * D * δq := (div_le_iff₀ hδ).mp hq
  have h2 : dK * B ≤ 3 * D * δq * B := mul_le_mul_of_nonneg_right h1 hB
  linarith

theorem share_numeric : ShareNum := by
  unfold ShareNum
  intro dK d0 d U δq ep y del hU hδ hdK hd0 hep hey hy hdel hdel' h1 h2 h3
  rw [div_le_iff₀ hδ]
  have k1 : 7 / 8 * dK ≤ U * d0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - ep) hdK]
  have k2 : 7 / 8 * U ≤ δq := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - y) hU.le]
  have k3 : 3 / 4 * d0 ≤ d := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - del) hd0]
  have hd : 0 ≤ d := by linarith
  have k4 : d * (7 / 8 * U) ≤ d * δq := mul_le_mul_of_nonneg_left k2 hd
  have k5 : 3 / 4 * d0 * U ≤ d * U := mul_le_mul_of_nonneg_right k3 hU.le
  nlinarith

theorem level_pair : LevelPair := by
  unfold LevelPair
  intro en enc T vs vsc nn nnc frn Dp Dm F h1 h2 hT hf hvs hvsc hn hF
  subst hvs hvsc hF
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem normaliser_pair : NormaliserPair := by
  unfold NormaliserPair
  intro K _ _ _ w π hπ Dp Dm
  have hV := Formalism.DivisionValues.valuation_basic_properties K w
  have hsπ : star π ≠ 0 := star_ne_zero.mpr hπ
  have hpow : ∀ x : K, x ≠ 0 → ∀ n : ℕ, Formalism.DivisionValues.vw w (x ^ n) = (n : ℤ) * Formalism.DivisionValues.vw w x := by
    intro x hx n
    induction n with
    | zero => simp [hV.2.2.2.2.1]
    | succ n ih =>
      rw [pow_succ, hV.1 _ _ (pow_ne_zero _ hx) hx, ih]
      push_cast
      ring
  rw [← hV.2.1, star_mul, star_pow, star_pow, star_star,
    hV.1 (star π ^ Dp) (π ^ Dm) (pow_ne_zero _ hsπ) (pow_ne_zero _ hπ),
    hV.1 (star π ^ Dm) (π ^ Dp) (pow_ne_zero _ hsπ) (pow_ne_zero _ hπ),
    hV.1 π (star π) hπ hsπ, hpow _ hsπ Dp, hpow _ hπ Dm, hpow _ hsπ Dm, hpow _ hπ Dp]
  ring

theorem unit_change' : UnitChange := by
  unfold UnitChange
  intro ρ x y d r k δ ε hρ hδ
  have hρ' : ρ ≠ 0 := hρ.ne'
  have hδ' : δ ≠ 0 := hδ.ne'
  first
    | (field_simp; ring)
    | field_simp

end Formalism.EigenvalueLevelCeiling
