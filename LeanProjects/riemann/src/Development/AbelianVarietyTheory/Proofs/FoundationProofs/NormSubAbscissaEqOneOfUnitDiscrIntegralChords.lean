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

variable {p : ℕ} [Fact p.Prime]

theorem norm_le_one_of_quad {a c m : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (h : ‖m ^ 2 + a * m - c‖ ≤ 1) : ‖m‖ ≤ 1 := by
  by_contra hm
  push_neg at hm
  have e : m ^ 2 = (m ^ 2 + a * m - c) + (-(a * m) + c) := by ring
  have hb : ‖m ^ 2‖ ≤ ‖m‖ := by
    rw [e]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (h.trans hm.le) ?_)
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (hc.trans hm.le))
    rw [norm_neg, norm_mul]
    calc ‖a‖ * ‖m‖ ≤ 1 * ‖m‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ = ‖m‖ := one_mul _
  rw [norm_pow, sq] at hb
  have : 1 * ‖m‖ < ‖m‖ * ‖m‖ := mul_lt_mul_of_pos_right hm (by linarith)
  linarith

theorem norm_sub_x_eq_one : ∀ {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (x₁ y₁ x₂ y₂ m m' : ℂ_[p]), ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.Δ‖ = 1 → W.toAffine.Equation x₁ y₁ → W.toAffine.Equation x₂ y₂ → ‖x₁‖ ≤ 1 → ‖x₂‖ ≤ 1 → x₁ ≠ x₂ → m * (x₁ - x₂) = y₁ - y₂ → m' * (x₁ - x₂) = y₁ - W.toAffine.negY x₂ y₂ → ‖m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂‖ ≤ 1 → ‖x₁ - x₂‖ = 1 := by
  intro p _ W x₁ y₁ x₂ y₂ m m' h1 h2 hΔ he1 he2 hx1 hx2 hne hm hm' hq hq'
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  have hle : ‖x₁ - x₂‖ ≤ 1 := by
    rw [sub_eq_add_neg]; exact it_add hx1 (by rwa [norm_neg])
  refine le_antisymm hle (not_lt.mp fun hs => ?_)
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have c12 : ‖W.a₂ + x₁ + x₂‖ ≤ 1 := it_add (it_add h2 hx1) hx2
  have mb : ‖m‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m ^ 2 + W.a₁ * m - (W.a₂ + x₁ + x₂) = m ^ 2 + W.a₁ * m - W.a₂ - x₁ - x₂ by ring])
  have mb' : ‖m'‖ ≤ 1 := norm_le_one_of_quad h1 c12
    (by rwa [show m' ^ 2 + W.a₁ * m' - (W.a₂ + x₁ + x₂) = m' ^ 2 + W.a₁ * m' - W.a₂ - x₁ - x₂ by ring])
  have s1 : ‖y₁ - y₂‖ < 1 := by rw [← hm, mul_comm]; exact sm_mul' hs mb
  have s2 : ‖y₁ + y₂ + W.a₁ * x₂ + W.a₃‖ < 1 := by
    have e : y₁ + y₂ + W.a₁ * x₂ + W.a₃ = m' * (x₁ - x₂) := by
      rw [hm']; simp only [WeierstrassCurve.Affine.negY]; ring
    rw [e, mul_comm]; exact sm_mul' hs mb'
  have s3 : ‖W.a₁ * (x₁ - x₂)‖ < 1 := sm_mul h1 hs
  have hy : ‖2 * y₁ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show 2 * y₁ + W.a₁ * x₁ + W.a₃ =
      (y₁ - y₂) + (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add (sm_add s1 s2) s3
  have s4 : ‖y₁ + y₂ + W.a₁ * x₁ + W.a₃‖ < 1 := by
    rw [show y₁ + y₂ + W.a₁ * x₁ + W.a₃ = (y₁ + y₂ + W.a₁ * x₂ + W.a₃) + W.a₁ * (x₁ - x₂) by ring]
    exact sm_add s2 s3
  have e1 := he1
  have e2 := he2
  rw [WeierstrassCurve.Affine.equation_iff] at e1 e2
  have hN : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂ =
      m * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) := by
    apply mul_right_cancel₀ hd
    have hsub : (y₁ - y₂) * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) = (x₁ - x₂) *
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) := by
      linear_combination e1 - e2
    linear_combination -hsub - (y₁ + y₂ + W.a₁ * x₁ + W.a₃) * hm
  have hN' : ‖x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂‖ < 1 := by
    rw [hN]; exact sm_mul mb s4
  have hx' : ‖3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁‖ < 1 := by
    rw [show 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ =
      (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂) -
        ((x₂ - x₁) * (x₂ + 2 * x₁ + W.a₂) + W.a₁ * (y₁ - y₂)) by ring]
    refine sm_sub hN' (sm_add ?_ (sm_mul h1 s1))
    exact sm_mul' (by rw [← norm_neg, neg_sub]; exact hs) (it_add (it_add hx2 (it_mul n2 hx1)) h2)
  have hc := disc_small W x₁ y₁ h1 h2 hx1 he1 hy hx'
  rw [hΔ] at hc
  exact lt_irrefl _ hc

end GlobalTheory.ThetaPar
