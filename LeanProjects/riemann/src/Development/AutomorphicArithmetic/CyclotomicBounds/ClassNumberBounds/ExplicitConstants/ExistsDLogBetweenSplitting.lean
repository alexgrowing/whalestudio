import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.UniformIffAboveThreshold
import Mathlib

open Filter Set Real

namespace KStar.Consta.Params

variable (P : Params)

structure RowsAt (X x : ℝ) (q₁ d n cond : ℕ) (t : ℝ) : Prop where
  p12 : x ^ (2 * P.Ct + 5) < q₁ ∧ x ^ (2 * P.Ct + 5) < d
  log_first_prime_le : Real.log q₁ ≤ x ^ (P.eps / 5)
  log_d_le_alt : Real.log d ≤ x ^ (P.eps / 5) * Real.log x ^ 2
  log_conductor_le : Real.log cond ≤ 2 * x ^ (P.eps / 5) * Real.log x ^ 2
  p13x : 2 * x ^ (P.eps / 5) * Real.log x ^ 2 ≤ P.L x / 100
  exp_power_le_min : Real.exp (x ^ (P.eps / (6 * P.K))) ≤ min (q₁ : ℝ) d
  exp_power_le_sqrt_d : Real.exp (x ^ (P.eps / (5 * P.K))) ≤ Real.sqrt d
  p15x : 11 ≤ x ^ (P.eps / 5)
  inert_primes_large : ∀ p : ℕ, p.Prime → ¬ SplitsIn d p → P.z X < p ∧ x ^ (P.eps / (5 * P.K)) < p
  power_le_exp_power : x ^ (2 * P.Ct) ≤ Real.exp (x ^ (P.eps / (5 * P.K)))
  p46 : P.Lw x ≤ 11 * (P.Ct + 4) * Real.log x
  log_product_small : Real.log (n * P.q * t * q₁ * d) ≤ x ^ P.eps / 400 ∧ 9 * t ^ 2 < min (q₁ : ℝ) d
  del : P.delZ X ≤ P.delX x ∧ P.delX x ≤ 1 / 8
  x2 : P.Lbar < x ^ (P.eps / 8)
  x4 : 16 * P.binaryExponentBound ≤ x ^ (2 * P.eps / 3)
  fact : P.L x ≤ (P.N5.factorial : ℝ) * Real.sqrt d

end KStar.Consta.Params
