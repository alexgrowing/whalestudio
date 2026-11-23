import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

theorem rankLie_bounds (d : IndexData) (e : Emb d) :
    1 ≤ (rankLie d e : ℝ) ∧ (rankLie d e : ℝ) ≤ d.N := by
  have h1 := d.one_le_j
  have h2 := d.j_lt_N
  unfold rankLie
  split_ifs
  · constructor
    · exact_mod_cast (by omega : 1 ≤ d.N - d.j)
    · exact_mod_cast (by omega : d.N - d.j ≤ d.N)
  · constructor
    · exact_mod_cast h1
    · exact_mod_cast h2.le

theorem geom_succ_inv (p : ℕ) (hp : 2 ≤ p) :
    HasSum (fun n : ℕ => ((p : ℝ) ^ (n + 1))⁻¹) (1 / ((p : ℝ) - 1)) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (p : ℝ)⁻¹
  have hfun : (fun n : ℕ => (p : ℝ)⁻¹ * (p : ℝ)⁻¹ ^ n) = fun n : ℕ => ((p : ℝ) ^ (n + 1))⁻¹ := by
    funext n
    rw [← inv_pow, pow_succ, mul_comm]
  rw [hfun] at h
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hsub : (1 : ℝ) - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  have hv : (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ = 1 / ((p : ℝ) - 1) := by
    rw [hsub, inv_div, ← mul_div_assoc, inv_mul_cancel₀ hp0]
  rw [hv] at h
  exact h

theorem KaPBound.proof : KaPBound.Statement := by
  intro d p φ hp _ τ
  have hp2 := hp.two_le
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hg := geom_succ_inv p hp2
  set a : ℕ → ℝ := fun n => ((p : ℝ) ^ (n + 1))⁻¹ with ha
  set r : ℕ → ℝ := fun n => (rankLie d ((φ ^ (n + 1)) (τ, false)) : ℝ) with hr
  have ha0 : ∀ n, 0 < a n := fun n => inv_pos.mpr (pow_pos (by linarith) _)
  have hterm0 : ∀ n, 0 ≤ a n * r n := fun n =>
    mul_nonneg (ha0 n).le (by linarith [(rankLie_bounds d ((φ ^ (n + 1)) (τ, false))).1])
  have htermle : ∀ n, a n * r n ≤ (d.N : ℝ) * a n := fun n => by
    rw [mul_comm (d.N : ℝ)]
    exact mul_le_mul_of_nonneg_left (rankLie_bounds d ((φ ^ (n + 1)) (τ, false))).2 (ha0 n).le
  have hNs : HasSum (fun n => (d.N : ℝ) * a n) ((d.N : ℝ) * (1 / ((p : ℝ) - 1))) := hg.mul_left _
  have hsum : Summable (fun n => a n * r n) :=
    Summable.of_nonneg_of_le hterm0 htermle hNs.summable
  have hk : kaP d p φ τ = ∑' n, a n * r n := rfl
  rw [hk]
  constructor
  · have h0 : 0 < a 0 * r 0 :=
      mul_pos (ha0 0) (by linarith [(rankLie_bounds d ((φ ^ (0 + 1)) (τ, false))).1])
    exact hsum.tsum_pos hterm0 0 h0
  · calc ∑' n, a n * r n ≤ ∑' n, (d.N : ℝ) * a n := hsum.tsum_le_tsum htermle hNs.summable
      _ = (d.N : ℝ) * (1 / ((p : ℝ) - 1)) := hNs.tsum_eq
      _ = (d.N : ℝ) / ((p : ℝ) - 1) := by ring

end GroundTheory.Heights₂.Heights.TheoremB
