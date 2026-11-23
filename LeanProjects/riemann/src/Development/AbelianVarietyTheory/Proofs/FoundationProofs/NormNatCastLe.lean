import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar

variable {p : ℕ} [Fact p.Prime]

def yAt (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 *
    (lamC g.lam (wpD g.abelian₂ v) / 2 - g.C.s * (lamC g.lam (wpF g.abelian₂ v) - g.C.r) - g.C.t)

theorem norm_natCast_le (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℂ_[p] n

theorem sm_add {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

theorem sm_sub {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add ha (by rwa [norm_neg])

theorem it_add {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)

theorem it_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb

theorem sm_mul {a b : ℂ_[p]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ 1 * ‖b‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact hb

theorem sm_mul' {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ < 1 := by
  rw [mul_comm]; exact sm_mul hb ha

theorem disc_small (W : WeierstrassCurve ℂ_[p]) (x y : ℂ_[p]) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (hx : ‖x‖ ≤ 1) (he : W.toAffine.Equation x y) (hy : ‖2 * y + W.a₁ * x + W.a₃‖ < 1)
    (hx' : ‖3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y‖ < 1) : ‖W.Δ‖ < 1 := by
  let C : WeierstrassCurve.VariableChange ℂ_[p] := ⟨1, x, 0, y⟩
  have hΔ : (C • W).Δ = W.Δ := by
    rw [WeierstrassCurve.variableChange_Δ]; simp [C]
  rw [WeierstrassCurve.Affine.equation_iff] at he
  have e1 : (C • W).a₁ = W.a₁ := by simp [C, WeierstrassCurve.variableChange_a₁]
  have e2 : (C • W).a₂ = W.a₂ + 3 * x := by simp [C, WeierstrassCurve.variableChange_a₂]
  have e3 : (C • W).a₃ = 2 * y + W.a₁ * x + W.a₃ := by
    simp [C, WeierstrassCurve.variableChange_a₃]; ring
  have e4 : (C • W).a₄ = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    simp [C, WeierstrassCurve.variableChange_a₄]; ring
  have e6 : (C • W).a₆ = 0 := by
    simp [C, WeierstrassCurve.variableChange_a₆]; linear_combination -he
  rw [← hΔ]
  have A1 : ‖(C • W).a₁‖ ≤ 1 := e1 ▸ h1
  have A2 : ‖(C • W).a₂‖ ≤ 1 := by
    rw [e2]; exact it_add h2 (it_mul (by simpa using norm_natCast_le (p := p) 3) hx)
  have A3 : ‖(C • W).a₃‖ < 1 := e3 ▸ hy
  have A4 : ‖(C • W).a₄‖ < 1 := e4 ▸ hx'
  set V := C • W
  have n4 : ‖(4 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 4
  have n2 : ‖(2 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 2
  have n8 : ‖(8 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 8
  have n27 : ‖(27 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 27
  have n9 : ‖(9 : ℂ_[p])‖ ≤ 1 := by simpa using norm_natCast_le (p := p) 9
  have B2 : ‖V.b₂‖ ≤ 1 := by
    rw [WeierstrassCurve.b₂]; exact it_add (by rw [sq]; exact it_mul A1 A1) (it_mul n4 A2)
  have B4 : ‖V.b₄‖ < 1 := by
    rw [WeierstrassCurve.b₄]; exact sm_add (sm_mul n2 A4) (sm_mul A1 A3)
  have B6 : ‖V.b₆‖ < 1 := by
    rw [WeierstrassCurve.b₆, e6, mul_zero, add_zero, sq]; exact sm_mul A3.le A3
  have BetaSesquilinearity : ‖V.b₈‖ < 1 := by
    rw [WeierstrassCurve.b₈, e6]
    simp only [mul_zero, add_zero]
    refine sm_sub (sm_add (sm_sub (by norm_num) (sm_mul (it_mul A1 A3.le) A4))
      (sm_mul A2 (by rw [sq]; exact sm_mul A3.le A3))) (by rw [sq]; exact sm_mul A4.le A4)
  rw [WeierstrassCurve.Δ]
  refine sm_add (sm_sub (sm_sub ?_ (sm_mul n8 (by rw [show V.b₄ ^ 3 = V.b₄ * V.b₄ * V.b₄ by ring]; exact sm_mul (it_mul B4.le B4.le) B4)))
    (sm_mul n27 (by rw [sq]; exact sm_mul B6.le B6))) (sm_mul (it_mul (it_mul n9 B2) B4.le) B6)
  rw [neg_mul]
  rw [norm_neg]; exact sm_mul (by rw [sq]; exact it_mul B2 B2) BetaSesquilinearity

end GlobalTheory.ThetaPar
