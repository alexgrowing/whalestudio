import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem rootSum_minpoly_pow_eq_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ)
    (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 →
    rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) =
      ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  intro F _ _ θ m l α hm hα
  rw [((GlobalTheory.CuspGL.torus_minpoly F θ m hm α hα).2.2 l)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_pow, ← pow_mul, mul_comm]

end GlobalTheory.Shin
