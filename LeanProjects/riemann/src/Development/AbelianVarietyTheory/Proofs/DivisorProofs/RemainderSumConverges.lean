import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NewPrimesSetDescriptionStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem abs_tsum_geom_bdd_le (r M : ℝ) (c : ℕ → ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (hc : ∀ n, |c n| ≤ M) :
    |∑' n : ℕ, r ^ (n + 1) * c n| ≤ 2 * M * r := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hc 0)
  have hs : HasSum (fun n : ℕ => (M * r) * (1 / 2 : ℝ) ^ n) ((M * r) * 2) := hasSum_geometric_two.mul_left _
  have := tsum_of_norm_bounded (f := fun n : ℕ => r ^ (n + 1) * c n) hs (fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 _), pow_succ]
    have h2 : r ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ h0 h1 n
    calc r ^ n * r * |c n| ≤ (1 / 2 : ℝ) ^ n * r * M := by gcongr; exact hc n
      _ = _ := by ring)
  rw [Real.norm_eq_abs] at this
  linarith

theorem summable_log_div_sq_nat : Summable (fun n : ℕ => Real.log n * ((n : ℝ) ^ 2)⁻¹) := by
  have hs : Summable (fun n : ℕ => 2 * (n : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (Real.summable_nat_rpow.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.log_natCast_nonneg n) (by positivity)) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hn'.le (by norm_num)
  have h2 : (n : ℝ) ^ (-(3 / 2) : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hn'.le, ← Real.rpow_add hn']
    norm_num
  rw [h2, ← mul_assoc]
  gcongr
  linarith

theorem abs_restTerm_le_log_div_sq {D : D7} (Y : ShimX D.what₂.Tau) (Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N) :
    ∃ C : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm Y p Q| ≤ C * (Real.log p * ((p : ℝ) ^ 2)⁻¹) := by
  let M : D.what₂.Tau → ℕ → ℝ := fun τ k => ∑ σ, |Y.chern (chLie Y.j (k - 1) σ * Q τ k)|
  refine ⟨∑ τ, ∑ k ∈ Finset.Icc 2 Y.N, (Nat.factorial k : ℝ) * (2 * M τ k), fun p hp => ?_⟩
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  unfold restTerm
  rw [abs_mul, abs_of_nonneg hl, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ hl
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk2 : 2 ≤ k := (Finset.mem_Icc.1 hk).1
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hpk : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk2
  have hr : ((p : ℝ) ^ k)⁻¹ ≤ ((p : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hpk
  have hr2 : ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith)
  have hM : 0 ≤ M τ k := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine (abs_tsum_geom_bdd_le _ (M τ k) _ (by positivity) (hr.trans hr2) (fun n => ?_)).trans ?_
  · exact Finset.single_le_sum (f := fun σ => |Y.chern (chLie Y.j (k - 1) σ * Q τ k)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  · gcongr

theorem restTerm_sum_tendsto : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (B₀ : ℝ) (Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N), 0 ≤ B₀ → ∃ L : ℝ, Tendsto (fun B : ℕ => ∑ p ∈ newPrimes Y B₀ B, restTerm Y p Q) atTop (𝓝 L) := by
  intro D Y B₀ Q hB
  obtain ⟨C, hC⟩ := abs_restTerm_le_log_div_sq Y Q
  let f : ℕ → ℝ := fun p => if p.Prime ∧ B₀ < (p : ℝ) ∧ ¬ p ∣ 2 * dE D ∧ p ∉ Y.lev then restTerm Y p Q else 0
  have hs : Summable f := by
    refine Summable.of_norm_bounded (summable_log_div_sq_nat.mul_left |C|) (fun p => ?_)
    have h0 : 0 ≤ Real.log p * ((p : ℝ) ^ 2)⁻¹ := mul_nonneg (Real.log_natCast_nonneg p) (by positivity)
    simp only [f, Real.norm_eq_abs]
    split_ifs with h
    · exact (hC p h.1.two_le).trans (mul_le_mul_of_nonneg_right (le_abs_self C) h0)
    · rw [abs_zero]; positivity
  refine ⟨∑' p, f p, ?_⟩
  have h1 := (hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  refine h1.congr fun n => ?_
  rw [(GlobalTheory.T.new_primes_set_description D Y B₀ B₀ hB).2.2.2 n, Finset.sum_filter]
  rfl

end GlobalTheory.Mean4
