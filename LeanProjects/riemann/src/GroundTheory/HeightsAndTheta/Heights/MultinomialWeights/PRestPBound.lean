import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset Filter Topology

def restCoeffBound (d : IndexData) (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) : ℝ :=
  ∑ e : Emb d, |((((k : ℚ) * intFl d (liePowerSum d (k - 1) e * Q k τ) : ℚ) : ℝ))|

theorem restCoeffBound_nonneg (d : IndexData) (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) :
    0 ≤ restCoeffBound d Q τ k :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem restSeries_abs_le (d : IndexData) (p : ℕ) (hp : 1 ≤ p) (φ : Equiv.Perm (Emb d))
    (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    |restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * ((p : ℝ) ^ 2)⁻¹ ^ (n + 1) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < p := by linarith
  calc |restSeries d p φ Q τ k n|
      = |((((k : ℚ) * intFl d (liePowerSum d (k - 1) ((φ ^ (n + 1)) (τ, false)) * Q k τ) : ℚ) : ℝ))| *
          ((p : ℝ) ^ ((n + 1) * k))⁻¹ := by
        unfold restSeries
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((p : ℝ) ^ ((n + 1) * k))⁻¹), mul_comm]
    _ ≤ restCoeffBound d Q τ k * ((p : ℝ) ^ 2)⁻¹ ^ (n + 1) := by
        apply mul_le_mul
        · unfold restCoeffBound
          exact Finset.single_le_sum
            (f := fun e : Emb d => |((((k : ℚ) * intFl d (liePowerSum d (k - 1) e * Q k τ) : ℚ) : ℝ))|)
            (fun e _ => abs_nonneg _) (mem_univ ((φ ^ (n + 1)) (τ, false)))
        · rw [inv_pow, ← pow_mul]
          apply inv_anti₀ (by positivity)
          apply pow_le_pow_right₀ hp'
          rw [mul_comm]
          exact Nat.mul_le_mul_left _ hk
        · positivity
        · exact restCoeffBound_nonneg d Q τ k

theorem restSeries_tsum_bound (d : IndexData) (p : ℕ) (hp : p.Prime) (φ : Equiv.Perm (Emb d))
    (Q : ℕ → Fin d.f → XPoly d) (τ : Fin d.f) (k : ℕ) (hk : 2 ≤ k) :
    Summable (restSeries d p φ Q τ k) ∧
      |∑' n : ℕ, restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ((p : ℝ) ^ 2)⁻¹ := ⟨_, rfl⟩
  rw [← hr]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 / 2 := by
    have h4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    rw [hr]
    calc ((p : ℝ) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h4
      _ ≤ 1 / 2 := by norm_num
  have hM := restCoeffBound_nonneg d Q τ k
  have hb : ∀ n : ℕ, |restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * (r * r ^ n) := by
    intro n
    rw [← pow_succ', hr]
    exact restSeries_abs_le d p hp.one_lt.le φ Q τ k hk n
  have hg : Summable (fun n : ℕ => restCoeffBound d Q τ k * (r * r ^ n)) :=
    ((summable_geometric_of_lt_one hr0 (by linarith)).mul_left r).mul_left _
  have hs : Summable (restSeries d p φ Q τ k) :=
    Summable.of_norm_bounded hg (fun n => by rw [Real.norm_eq_abs]; exact hb n)
  have habs : Summable (fun n : ℕ => |restSeries d p φ Q τ k n|) :=
    Summable.of_norm_bounded hg (fun n => by rw [Real.norm_eq_abs, abs_abs]; exact hb n)
  refine ⟨hs, ?_⟩
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc |∑' n : ℕ, restSeries d p φ Q τ k n|
      ≤ ∑' n : ℕ, |restSeries d p φ Q τ k n| := by
        have := norm_tsum_le_tsum_norm (f := restSeries d p φ Q τ k)
          (by simpa only [Real.norm_eq_abs] using habs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, restCoeffBound d Q τ k * (r * r ^ n) := Summable.tsum_le_tsum hb habs hg
    _ = restCoeffBound d Q τ k * (r * (1 - r)⁻¹) := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith)]
    _ ≤ restCoeffBound d Q τ k * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ hM
        calc r * (1 - r)⁻¹ ≤ r * 2 := mul_le_mul_of_nonneg_left hinv hr0
          _ = 2 * r := mul_comm _ _

theorem RestPBound.proof : RestPBound.Statement := by
  intro d vol F Q _
  refine ⟨2 * |vol| * ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k, ?_⟩
  intro p φ hp
  have key : ∀ τ : Fin d.f, ∀ k ∈ Icc 2 d.N,
      Summable (restSeries d p φ Q τ k) ∧
        |∑' n : ℕ, restSeries d p φ Q τ k n| ≤ restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) :=
    fun τ k hk => restSeries_tsum_bound d p hp φ Q τ k (mem_Icc.mp hk).1
  refine ⟨fun τ k hk => (key τ k hk).1, ?_⟩
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hsum : |∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n| ≤
      ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) :=
    calc |∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n|
        ≤ ∑ τ : Fin d.f, |∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, |∑' n : ℕ, restSeries d p φ Q τ k n| :=
          sum_le_sum fun τ _ => abs_sum_le_sum_abs _ _
      _ ≤ _ := sum_le_sum fun τ _ => sum_le_sum fun k hk => (key τ k hk).2
  calc |rest₂ d vol p φ Q|
      = Real.log p * |vol| * |∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, ∑' n : ℕ, restSeries d p φ Q τ k n| := by
        unfold rest₂
        rw [abs_mul, abs_mul, abs_of_nonneg hlog]
    _ ≤ Real.log p * |vol| *
          ∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k * (2 * ((p : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hlog (abs_nonneg _))
    _ = 2 * |vol| * (∑ τ : Fin d.f, ∑ k ∈ Icc 2 d.N, restCoeffBound d Q τ k) * Real.log p /
          (p : ℝ) ^ 2 := by
        simp only [← Finset.sum_mul]
        rw [div_eq_mul_inv]
        ring

end GroundTheory.Heights₂.Heights.TheoremB
