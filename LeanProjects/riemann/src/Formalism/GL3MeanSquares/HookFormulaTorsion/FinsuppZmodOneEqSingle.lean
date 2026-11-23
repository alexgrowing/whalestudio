import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
import Formalism.LogVandermondeBounds.LogVandermondeProofs.TaylorLogMetric
import Formalism.GL3MeanSquares.HookFormulaTorsion.CocycleIsCoboundary

namespace Formalism.HermitianLattices.IntegralLatticeDensity

namespace LemE

open MvPowerSeries Finset Formalism.G Formalism.FG

noncomputable abbrev s1 (n : ℕ) : ZMod 1 →₀ ℕ := Finsupp.single 0 n

noncomputable abbrev mon (k m : ℕ) : Fin 2 × ZMod 1 →₀ ℕ :=
  Finsupp.single ((0 : Fin 2), (0 : ZMod 1)) k + Finsupp.single ((1 : Fin 2), (0 : ZMod 1)) m

section Generic

variable {K : Type} [Field K] {τ : Type}

lemma coeff_add_pow (k m : ℕ) :
    coeff (mon k m) ((X ((0 : Fin 2), (0 : ZMod 1)) + X ((1 : Fin 2), (0 : ZMod 1)) :
      MvPowerSeries (Fin 2 × ZMod 1) K) ^ (k + m)) = ((k + m).choose k : K) := by
  classical
  rw [add_pow, map_sum, Finset.sum_eq_single k]
  · rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, Nat.add_sub_cancel_left, ← nsmul_eq_mul',
      map_nsmul, coeff_monomial_same]
    simp
  · intro j _ hj
    rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, ← nsmul_eq_mul', map_nsmul, coeff_monomial,
      if_neg, smul_zero]
    intro h
    have := congrArg (fun d => d ((0 : Fin 2), (0 : ZMod 1))) h
    simp at this
    exact hj this.symm
  · intro h
    exact absurd (mem_range.2 (by omega)) h

end Generic

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

end Padic

section Main

variable {p : ℕ} [hp : Fact p.Prime]

def Good (f : MvPowerSeries (ZMod 1) ℚ_[p]) (N : ℕ) (z : ℚ_[p] × ℚ_[p]) : Prop :=
  ‖z.1‖ ≤ 1 ∧ ‖z.2 - coeff (s1 1) f‖ ≤ 1 ∧
    ∀ d ≤ N, ‖coeff (s1 d) f - z.1 * coeff (s1 d) (g0 p) -
      z.2 * coeff (s1 d) (shiftLog ℚ_[p] p 1 0)‖ ≤ 1

end Main

end LemE

end Formalism.HermitianLattices.IntegralLatticeDensity
