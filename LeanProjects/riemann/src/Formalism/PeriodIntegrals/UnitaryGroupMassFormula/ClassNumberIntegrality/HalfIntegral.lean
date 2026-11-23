import Mathlib
import Formalism.PeriodIntegrals.ClassNumImQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDifference.QuadraticDifferenceForm

noncomputable section

namespace PI.UnitaryGroupMassFormula.ClassNumImQInt

open NumberField Polynomial

theorem adjoin_top {K : Type} [Field K] [NumberField K] (b : K)
    (h : IntermediateField.adjoin ℚ {b} = ⊤) : Algebra.adjoin ℚ {b} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic b), h]
  exact IntermediateField.top_toSubalgebra

theorem half_integral {K : Type} [Field K] [NumberField K] (d : ℕ) (b : K) (hd : d % 4 = 3)
    (hb : b ^ 2 = -(d : K)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hk' : (d : K) + 1 = 4 * (k : K) := by exact_mod_cast hk
  refine ⟨X ^ 2 - X + C (k : ℤ), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_natCast, map_natCast]
  linear_combination (1 / 4 : K) * hb - (1 / 4 : K) * hk'

theorem intBasis : PI.ClassNumImQ.IntBasis := by
  intro d K _ _ b ⟨hp, hd, _, hb, htop⟩
  have hsq : Squarefree d := hp.prime.squarefree
  have htop' := adjoin_top b htop
  refine ⟨half_integral d b hd hb, ?_⟩
  intro z
  obtain ⟨x, y, hxy⟩ := PI.QD.quadratic_difference_form K d b hb htop' (z : K)
  have hint : IsIntegral ℤ ((x : K) + (y : K) * b) := by rw [← hxy]; exact z.isIntegral_coe
  obtain ⟨h2x, hN⟩ := PI.QD.quadratic_intCoeffs K d b x y hsq hd hb hint
  obtain ⟨a, v, hx, hy⟩ := PI.QD.quadraticDifferenceArith d x y hsq hd h2x hN
  refine ⟨a, v, ?_⟩
  rw [hxy, hx, hy]
  push_cast
  ring

end PI.UnitaryGroupMassFormula.ClassNumImQInt
