import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem pderiv_lineClass (d : IndexData) (u : Idx d → ℚ) (p : Idx d) :
    pderiv p (lineClass d u) = C (-(u p)) := by
  classical
  simp only [lineClass, lamDotX, map_neg, map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_pderiv_lineClass_pow (d : IndexData) (τ : Fin d.f) (u : Idx d → ℚ) :
    ∑ i : Fin d.N, pderiv (τ, i) (lineClass d u ^ (d.D + 1)) =
      C (-((d.D + 1 : ℕ) : ℚ) * ∑ i : Fin d.N, u (τ, i)) * lineClass d u ^ d.D := by
  simp only [pderiv_pow, pderiv_lineClass, Nat.add_sub_cancel]
  rw [Finset.mul_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_neg, map_natCast]
  ring

theorem TotOfPower.proof : TotOfPower.Statement := by
  intro d τ u
  rw [totalFl, sum_pderiv_lineClass_pow, ← smul_eq_C_mul, map_smul, smul_eq_mul, degAt]
  ring

end GroundTheory.Heights₂.Heights.TheoremB
