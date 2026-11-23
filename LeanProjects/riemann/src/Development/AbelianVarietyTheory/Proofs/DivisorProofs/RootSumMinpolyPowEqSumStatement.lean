import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSum
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ) (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 → rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  first | (exact @GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (exact GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (intros; apply GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum  <;> assumption)
