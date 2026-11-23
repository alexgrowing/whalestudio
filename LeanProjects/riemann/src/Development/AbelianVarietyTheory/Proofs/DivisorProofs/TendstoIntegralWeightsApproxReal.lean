import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
open MvPolynomial GlobalTheory.FlagPoly Formalism.DegreeFormula Filter Topology

namespace GlobalTheory.WeightApprox

theorem linRoot_smul {ι : Type} [Fintype ι] {N : ℕ} (t : ℝ) (w : ι → Fin N → ℝ) :
    linRoot (fun τ i => t * w τ i) = C t * linRoot w := by
  unfold linRoot
  rw [mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [C_mul, mul_assoc]

theorem continuous_comp_of_filtered_continuity {ι : Type} [Fintype ι] {N : ℕ} (Φ : Pol ι N →ₗ[ℝ] ℝ) (d : ℕ) :
    ∀ Q : Pol ι N, Continuous (fun lam : ι → Fin N → ℝ => Φ (linRoot lam ^ d * Q)) := by
  induction d with
  | zero => intro Q; simp only [pow_zero, one_mul]; exact continuous_const
  | succ d ih =>
    intro Q
    have key : ∀ lam : ι → Fin N → ℝ, Φ (linRoot lam ^ (d + 1) * Q) =
        -∑ x : ι × Fin N, lam x.1 x.2 * Φ (linRoot lam ^ d * (X x * Q)) := by
      intro lam
      have hL : ∀ R : Pol ι N, linRoot lam * R = -∑ x : ι × Fin N, C (lam x.1 x.2) * (X x * R) := by
        intro R
        unfold linRoot
        rw [neg_mul, Finset.sum_mul]
        simp only [mul_assoc]
      have : linRoot lam ^ (d + 1) * Q =
          -∑ x : ι × Fin N, C (lam x.1 x.2) * (linRoot lam ^ d * (X x * Q)) := by
        rw [pow_succ', mul_assoc, hL]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
      rw [this, map_neg, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [C_mul', map_smul, smul_eq_mul]
    simp_rw [key]
    refine Continuous.neg (continuous_finset_sum _ fun x _ => ?_)
    have hc : Continuous fun lam : ι → Fin N → ℝ => lam x.1 x.2 := by fun_prop
    exact hc.mul (ih (X x * Q))

theorem approx : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Φ : Pol ι N →ₗ[ℝ] ℝ) (d : ℕ) (lam : ι → Fin N → ℝ), ∃ (u : ℕ → ι → Fin N → ℤ) (c : ℕ → ℝ), (∀ m, 0 < c m) ∧ (∀ m τ (a b : Fin N), lam τ a ≤ lam τ b → u m τ a ≤ u m τ b) ∧ Tendsto (fun m => c m * Φ (linRoot (fun τ i => (u m τ i : ℝ)) ^ d)) atTop (𝓝 (Φ (linRoot lam ^ d))) := by
  intro ι _ N Φ d lam
  refine ⟨fun m τ i => ⌊((m : ℝ) + 1) * lam τ i⌋, fun m => 1 / ((m : ℝ) + 1) ^ d, ?_, ?_, ?_⟩
  · intro m; positivity
  · intro m τ a b h
    exact Int.floor_mono (mul_le_mul_of_nonneg_left h (by positivity))
  · have hcont : Continuous (fun w : ι → Fin N → ℝ => Φ (linRoot w ^ d)) := by
      simpa using continuous_comp_of_filtered_continuity Φ d 1
    set v : ℕ → ι → Fin N → ℝ := fun m τ i => 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ)
      with hv
    have heq : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ^ d *
        Φ (linRoot (fun τ i => ((⌊((m : ℝ) + 1) * lam τ i⌋ : ℤ) : ℝ)) ^ d) = Φ (linRoot (v m) ^ d) := by
      intro m
      rw [hv]
      simp only
      rw [linRoot_smul, mul_pow, ← C_pow, C_mul', map_smul, smul_eq_mul, one_div_pow]
    simp_rw [heq]
    have hlim : Tendsto v atTop (𝓝 lam) := by
      rw [tendsto_pi_nhds]; intro τ
      rw [tendsto_pi_nhds]; intro i
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      have hlow : Tendsto (fun m : ℕ => lam τ i - 1 / ((m : ℝ) + 1)) atTop (𝓝 (lam τ i)) := by
        have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => lam τ i) atTop (𝓝 (lam τ i))).sub h0
        simpa using h2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
      · intro m
        have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have h1 := Int.sub_one_lt_floor (((m : ℝ) + 1) * lam τ i)
        show lam τ i - 1 / ((m : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ)
        rw [one_div_mul_eq_div, le_div_iff₀ hp, sub_mul, one_div_mul_cancel hp.ne']
        linarith
      · intro m
        have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have h1 := Int.floor_le (((m : ℝ) + 1) * lam τ i)
        show 1 / ((m : ℝ) + 1) * (⌊((m : ℝ) + 1) * lam τ i⌋ : ℝ) ≤ lam τ i
        rw [one_div, inv_mul_eq_div, div_le_iff₀ hp]
        linarith
    exact (hcont.tendsto lam).comp hlim

end GlobalTheory.WeightApprox
