import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem rest_bound (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (k : ℕ) (Q : RP Ψ N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (p : ℕ) (fr : ℕ → Ψ ⊕ Ψ), 2 ≤ p →
      |restTerm j p fr k Q| ≤ c * Real.log p / (p : ℝ) ^ 2 := by
  set M : ℝ := ∑ σ : Ψ ⊕ Ψ, |degFl (pLie j (k - 1) σ * Q)| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMle : ∀ σ, |degFl (pLie j (k - 1) σ * Q)| ≤ M := fun σ =>
    Finset.single_le_sum (f := fun σ => |degFl (pLie j (k - 1) σ * Q)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ)
  refine ⟨2 * k * M, by positivity, fun p fr hp => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restTerm
  split_ifs with hk
  · set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr
    have hr0 : 0 ≤ r := by positivity
    have hpk : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk
    have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hr1 : r ≤ ((p : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hpk
    have hr2 : r ≤ 1 / 2 := by
      refine hr1.trans ?_
      rw [one_div]
      exact inv_anti₀ (by norm_num) (by linarith)
    have hs : HasSum (fun n : ℕ => (r * M) * (1 / 2 : ℝ) ^ n) ((r * M) * 2) :=
      hasSum_geometric_two.mul_left _
    have hb : ‖∑' n : ℕ, r ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q)‖ ≤ (r * M) * 2 := by
      refine tsum_of_norm_bounded hs fun n => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ (n + 1)), pow_succ]
      have h1 : r ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hr0 hr2 n
      calc r ^ n * r * |degFl (pLie j (k - 1) (fr n) * Q)| ≤ (1 / 2 : ℝ) ^ n * r * M := by
            gcongr
            exact hMle _
        _ = _ := by ring
    rw [Real.norm_eq_abs] at hb
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.log p * (k : ℝ))]
    calc Real.log p * (k : ℝ) * |∑' n : ℕ, r ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q)|
        ≤ Real.log p * (k : ℝ) * ((((p : ℝ) ^ 2)⁻¹ * M) * 2) := by
          gcongr
          refine hb.trans ?_
          gcongr
      _ = _ := by ring
  · rw [abs_zero]
    positivity

theorem summable_log_div_sq : Summable fun p : ℕ => Real.log p / (p : ℝ) ^ 2 := by
  have h : Summable fun p : ℕ => 2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun p => div_nonneg (Real.log_natCast_nonneg p) (by positivity))
    (fun p => ?_) h
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 := Real.log_le_rpow_div hp'.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (p : ℝ) ^ 2 = (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hp']
    norm_num
  have h3 : 0 < (p : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have h4 : 0 < (p : ℝ) ^ (3 / 2 : ℝ) := by positivity
  rw [h2, div_le_iff₀ (by positivity)]
  refine h1.trans (le_of_eq ?_)
  field_simp

theorem rest_term_bound_convergent : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) := by
  intro Ψ _ _ N j bad frob τ k Q
  obtain ⟨c, hc0, hc⟩ := rest_bound Ψ N j k Q
  refine ⟨⟨c, fun p hp => hc p _ hp⟩, fun B₀ => ?_⟩
  have hs : Summable fun p : ℕ =>
      if p.Prime ∧ B₀ < p ∧ p ∉ bad then restTerm j p (frob p τ) k Q else 0 := by
    refine Summable.of_norm_bounded (summable_log_div_sq.mul_left c) fun p => ?_
    split_ifs with h
    · rw [Real.norm_eq_abs, ← mul_div_assoc]
      exact hc p _ h.1.two_le
    · rw [norm_zero]
      exact mul_nonneg hc0 (div_nonneg (Real.log_natCast_nonneg p) (by positivity))
  have ht := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine ht.congr fun B => ?_
  simp only [Function.comp_apply]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h3, by omega⟩, h2, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, h3, h1, h4⟩

end RootFieldNumerics
