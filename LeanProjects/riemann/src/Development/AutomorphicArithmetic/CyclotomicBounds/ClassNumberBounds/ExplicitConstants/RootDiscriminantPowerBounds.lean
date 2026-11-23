import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.ExistsDLogBetweenSplitting
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.PowerBoundWithOrderConstant
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.TopDefs

open Filter Set Real

namespace KStar.Consta.Params

variable (P : Params)

structure RowsAtH (o : ℕ) (C X x : ℝ) (q₁ d n cond : ℕ) (t : ℝ) : Prop
    extends P.RowsAt X x q₁ d n cond t where
  loglog : 1 ≤ Real.log (Real.log x)
  cond_alt : Real.log cond ≤ 3 * P.z' X
  x4H : 16 * P.CT o ≤ x ^ (2 * P.eps / 3)
  power_le_size_over_log : 6 * x ^ 5 ≤ (q₁ : ℝ) / Real.log q₁ ∧ 6 * x ^ 5 ≤ (d : ℝ) / Real.log d
  cubic_delta_bounds : 385 * x ^ C * x ^ C * x ^ C * P.delX x ≤ 1 ∧ 385 * x ^ C * x ^ C * x ^ C * P.delZ X ≤ 1
  root_discriminant_power_bounds : ∀ rd : ℝ, Real.sqrt d ≤ rd → Real.exp (P.z X) ≤ rd ^ 7 ∧ x ^ (2 * P.Ct) ≤ rd ^ 7
  inert_prime_digit_bound : ∀ (l j : ℕ) (lA : ℝ), l.Prime → ¬ SplitsIn d l → lA ≤ x ^ 5 →
    IsLeast {i : ℕ | lA ≤ ((l : ℝ) - 1) ^ i} j →
      j ≤ P.jmax ∧ 2 * (j : ℝ) + 2 ≤ P.Lw x ∧ (j : ℝ) + 1 ≤ P.Jeps
  l2 : ∀ (k : ℝ) (S : Set ℕ), 1 ≤ k → k ≤ 2 * x ^ (9 / 2 + 10 * P.eps) →
    (∀ p ∈ S, p.Prime ∧ ¬ SplitsIn d p) → (L2 k x S : ℝ) ≤ P.Lbar
  de2 : x ^ (-P.eps) ≤ 1 / (4 * P.Lw x)
  pair : 8 * P.q < q₁ ∧ 8 * P.q < d ∧ jacobiSym (-(q₁ : ℤ)) d = -1

end KStar.Consta.Params
