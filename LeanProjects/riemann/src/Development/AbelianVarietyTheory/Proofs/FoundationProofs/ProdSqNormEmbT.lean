import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuadraticCharNegOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.TypeNormProduct

theorem prod_sq_norm_embT : ∀ (D : D7) (y : 𝓞 D.host.E),
    ∏ τ, ‖embT D τ (y : D.host.E)‖ ^ 2 = (Ideal.absNorm (Ideal.span {y}) : ℝ) := by
  intro D y
  have hc : ∀ (φ : D.host.E →+* ℂ) (x : D.host.E), φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
    fun φ x => D.host.conjE_apply φ x
  have hcc : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x =>
    D.host.φ₀.injective (by rw [hc, hc, Complex.conj_conj])
  set x : D.host.E := (y : D.host.E) with hx
  have ht : D.host.conj (x * D.host.conj x) = x * D.host.conj x := by
    rw [map_mul, hcc, mul_comm]
  have h1 := GlobalTheory.NormSign.prod_embT D (x * D.host.conj x)
  have h2 := congrArg D.host.φ₀ (GlobalTheory.NormSign.norm_eq D.host ht)
  rw [map_pow, ← h1, map_ratCast, map_mul, Algebra.norm_eq_of_algEquiv] at h2
  have h3 : ∏ τ, embT D τ (x * D.host.conj x) = ((∏ τ, ‖embT D τ x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [h3] at h2
  have h4 : ((Algebra.norm ℚ x : ℚ) : ℝ) ^ 2 = (∏ τ, ‖embT D τ x‖ ^ 2) ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow, Complex.ofReal_pow, ← h2]
    push_cast
    ring
  have h5 : 0 ≤ ∏ τ, ‖embT D τ x‖ ^ 2 := Finset.prod_nonneg fun _ _ => by positivity
  rw [← sq_abs] at h4
  have h6 := (pow_left_inj₀ (abs_nonneg _) h5 two_ne_zero).1 h4
  rw [← h6, Ideal.absNorm_span_singleton, hx, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

end GlobalTheory.TypeNormProduct
