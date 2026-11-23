import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPowMemOfMulMemPow

namespace GlobalTheory

theorem exists_pow_mem_of_mul_mem_pow :
    ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A),
      (∀ a, δ * a = 0 → a = 0) → ∀ j : ℕ, ∃ k : ℕ, j ≤ k ∧ ∀ a, δ * a ∈ m ^ k → a ∈ m ^ j :=
  _root_.UpperTheory.Reformulated.B.Qg1.exists_pow_mem_of_mul_mem_pow

end GlobalTheory
