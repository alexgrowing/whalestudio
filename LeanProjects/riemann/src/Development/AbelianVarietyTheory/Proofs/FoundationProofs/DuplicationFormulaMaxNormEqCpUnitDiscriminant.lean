import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.DupNorm

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem i_add {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem i_sub {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 :=
  by rw [sub_eq_add_neg]; exact i_add ha (by rwa [norm_neg])

theorem i_mul {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem i_pow {a : K} (ha : ‖a‖ ≤ 1) (n : ℕ) : ‖a ^ n‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

theorem i_ofNat (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one K (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

theorem i_neg {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by rwa [norm_neg]

theorem i_one : ‖(1 : K)‖ ≤ 1 := by simp

theorem b_le (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) :
    ‖W.b₂‖ ≤ 1 ∧ ‖W.b₄‖ ≤ 1 ∧ ‖W.b₆‖ ≤ 1 ∧ ‖W.b₈‖ ≤ 1 := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg

theorem delta_eq (W : WeierstrassCurve K) (x : K) :
    W.Δ = (-48 * x ^ 2 - 8 * W.b₂ * x + (W.b₂ ^ 2 - 32 * W.b₄)) *
        (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) +
      (12 * x ^ 3 - W.b₂ * x ^ 2 - 10 * W.b₄ * x + (W.b₂ * W.b₄ - 27 * W.b₆)) *
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem max_norm_eq (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) (hΔ : ‖W.Δ‖ = 1) (x : K) :
    max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ =
      max 1 ‖x‖ ^ 4 := by
  obtain ⟨b2, b4, b6, b8⟩ := b_le W h1 h2 h3 h4 h6
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · have hp : ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    have hq : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ ≤ 1 := by repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
    rw [max_eq_left hx, one_pow]
    refine le_antisymm (max_le hp hq) ?_
    rw [← hΔ, delta_eq W x]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_) <;> rw [norm_mul] <;>
      refine mul_le_of_le_one_left (norm_nonneg _) ?_ <;> repeat' first | exact i_ofNat _ | exact i_one | assumption | apply i_add | apply i_sub | apply i_mul | apply i_pow | apply i_neg
  · have hR1 : 1 ≤ ‖x‖ := hx.le
    have bd : ∀ {c : K}, ‖c‖ ≤ 1 → ∀ {k m : ℕ}, k ≤ m → ‖c * x ^ k‖ ≤ ‖x‖ ^ m := by
      intro c hc k m hkm
      rw [norm_mul, norm_pow]
      calc ‖c‖ * ‖x‖ ^ k ≤ 1 * ‖x‖ ^ m :=
            mul_le_mul hc (pow_le_pow_right₀ hR1 hkm) (by positivity) zero_le_one
        _ = ‖x‖ ^ m := one_mul _
    have hφ : x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ =
        x ^ 4 + -(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0) := by ring
    have hψ : 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
        4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0 := by ring
    have hr : ‖W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0‖ ≤ ‖x‖ ^ 2 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (bd b4 le_rfl) (bd (i_mul (i_ofNat 2) b6) (by norm_num)))) (bd b8 (by norm_num)))
    have hs : ‖4 * x ^ 3 + W.b₂ * x ^ 2 + (2 * W.b₄) * x ^ 1 + W.b₆ * x ^ 0‖ ≤ ‖x‖ ^ 3 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans
            (max_le (bd (i_ofNat 4) le_rfl) (bd b2 (by norm_num))))
          (bd (i_mul (i_ofNat 2) b4) (by norm_num)))) (bd b6 (by norm_num)))
    have h24 : ‖x‖ ^ 2 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have h34 : ‖x‖ ^ 3 < ‖x‖ ^ 4 := pow_lt_pow_right₀ hx (by norm_num)
    have hne : ‖x ^ 4‖ ≠ ‖-(W.b₄ * x ^ 2 + (2 * W.b₆) * x ^ 1 + W.b₈ * x ^ 0)‖ := by
      rw [norm_neg, norm_pow]; exact (hr.trans_lt h24).ne'
    rw [hφ, hψ, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_pow,
      max_eq_left (hr.trans h24.le), max_eq_left (hs.trans h34.le), max_eq_right hR1]

theorem max_norm_eq_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]),
    ‖W.a₁‖ ≤ 1 → ‖W.a₂‖ ≤ 1 → ‖W.a₃‖ ≤ 1 → ‖W.a₄‖ ≤ 1 → ‖W.a₆‖ ≤ 1 → ‖W.Δ‖ = 1 →
      ∀ x : ℂ_[p], max ‖x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈‖
        ‖4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆‖ = max 1 ‖x‖ ^ 4 :=
  fun _ _ W h1 h2 h3 h4 h6 hΔ x => max_norm_eq W h1 h2 h3 h4 h6 hΔ x

end GlobalTheory.DupNorm
