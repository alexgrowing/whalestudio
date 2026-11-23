import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigA

open Complex Matrix ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

theorem projPerp_self {N : ℕ} (g0 : Fin N → ℂ) (h : g0 ≠ 0) : projPerp g0 *ᵥ g0 = 0 := by
  have hs : (sqNorm g0 : ℂ) ≠ 0 := by
    exact_mod_cast (sqNorm_pos h).ne'
  have e : star g0 ⬝ᵥ g0 = (sqNorm g0 : ℂ) := by
    simp [sqNorm, dotProduct, Complex.normSq_eq_conj_mul_self]
  funext i
  simp only [projPerp, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  rw [show (vecMulVec g0 (star g0) *ᵥ g0) i = g0 i * (star g0 ⬝ᵥ g0) by
    simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_assoc], e]
  field_simp
  ring

end BigA

end ReciprocityTheory.ChartRestriction.G.AR.Up
