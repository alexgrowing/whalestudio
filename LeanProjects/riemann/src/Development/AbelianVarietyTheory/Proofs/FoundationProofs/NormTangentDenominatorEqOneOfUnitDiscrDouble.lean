import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaPar

theorem padicComplex_norm_le_max_norm_add_norm {p : ℕ} [Fact p.Prime] {a b : ℂ_[p]} :
    ‖a‖ ≤ max ‖a + b‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max (a + b) (-b)
  simpa using this

theorem unit_of_double_integral_sub {p : ℕ} [Fact p.Prime] (a b : ℂ_[p]) :
    ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := IsUltrametricDist.norm_add_le_max a (-b)
  simpa [sub_eq_add_neg] using this

theorem unit_of_double_integral {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x y m : ℂ_[p])
    (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1)
    (hΔ : ‖W.Δ‖ = 1) (he : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1)
    (_hη : 2 * y + W.a₁ * x + W.a₃ ≠ 0)
    (hm : m * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y)
    (hm2 : ‖m ^ 2 + W.a₁ * m - W.a₂ - 2 * x‖ ≤ 1) :
    ‖2 * y + W.a₁ * x + W.a₃‖ = 1 := by
  have he' := he
  rw [WeierstrassCurve.Affine.equation_iff] at he'
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2

  have hy : ‖y‖ ≤ 1 := by
    by_contra hy
    push_neg at hy
    have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
      refine it_add (it_add (it_add ?_ (it_mul h2 ?_)) (it_mul h4 hx)) h6
      · rw [show x ^ 3 = x * x * x by ring]; exact it_mul (it_mul hx hx) hx
      · rw [sq]; exact it_mul hx hx
    have hS : ‖(W.a₁ * x + W.a₃) * y‖ ≤ ‖y‖ := by
      rw [norm_mul]
      calc ‖W.a₁ * x + W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ :=
            mul_le_mul_of_nonneg_right (it_add (it_mul h1 hx) h3) (norm_nonneg _)
        _ = ‖y‖ := one_mul _
    have hyy : ‖y‖ < ‖y ^ 2‖ := by
      rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := y ^ 2) (b := (W.a₁ * x + W.a₃) * y)
    have hsum : y ^ 2 + (W.a₁ * x + W.a₃) * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
      linear_combination he'
    rw [hsum] at key
    have : ‖y ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hR
      · exact absurd (h.trans hS) (not_le.mpr hyy)
    linarith
  have hηle : ‖2 * y + W.a₁ * x + W.a₃‖ ≤ 1 :=
    it_add (it_add (it_mul n2 hy) (it_mul h1 hx)) h3
  refine le_antisymm hηle (not_lt.mp fun hlt => ?_)

  have hmi : ‖m‖ ≤ 1 := by
    by_contra hmg
    push_neg at hmg
    have hT : ‖W.a₁ * m - W.a₂ - 2 * x‖ ≤ ‖m‖ := by
      have hm1 : (1 : ℝ) ≤ ‖m‖ := hmg.le
      refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ ?_)
      · refine le_trans (unit_of_double_integral_sub _ _) (max_le ?_ (h2.trans hm1))
        rw [norm_mul]
        calc ‖W.a₁‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = ‖m‖ := one_mul _
      · exact (it_mul n2 hx).trans hm1
    have hmm : ‖m‖ < ‖m ^ 2‖ := by rw [norm_pow, sq]; nlinarith
    have key := padicComplex_norm_le_max_norm_add_norm (a := m ^ 2) (b := W.a₁ * m - W.a₂ - 2 * x)
    rw [show m ^ 2 + (W.a₁ * m - W.a₂ - 2 * x) = m ^ 2 + W.a₁ * m - W.a₂ - 2 * x by ring] at key
    have : ‖m ^ 2‖ ≤ 1 := by
      rcases le_max_iff.mp key with h | h
      · exact h.trans hm2
      · exact absurd (h.trans hT) (not_le.mpr hmm)
    nlinarith [norm_nonneg m, show ‖m ^ 2‖ = ‖m‖ * ‖m‖ by rw [norm_pow, sq]]
  have hsmall : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1 := by
    rw [← hm]; exact sm_mul hmi hlt
  have := disc_small W x y h1 h2 hx he hlt hsmall
  linarith

end GlobalTheory.ThetaPar
