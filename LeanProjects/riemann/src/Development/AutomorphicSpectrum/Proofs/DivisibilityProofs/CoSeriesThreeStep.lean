import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem co_series_three_step : (∀ (Sg : Type) [Fintype Sg] [DecidableEq Sg] (φ : Equiv.Perm Sg) (p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ (La : Sg → ℝ) (τ : Sg), ∑ σ, co φ p k τ σ * La σ = (∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * La ((φ ^ (n + 1)) τ)) - La τ / ((p : ℝ) - 1)) ∧ (∀ (Sg : Type) (φ : Equiv.Perm Sg) (p k : ℕ), 2 ≤ p → ∀ (La : Sg → ℝ) (q : ℕ → Sg → ℝ), (∀ r τ, q r τ = ((p : ℝ) ^ ((r + 1) * k))⁻¹ * La ((φ ^ (r + 1)) τ) + q (r + 1) τ) → (∀ r τ, q (r + 1) τ = ((p : ℝ) ^ k)⁻¹ * q r (φ τ)) → ∀ τ, (p : ℝ) ^ k * q 0 τ = q 0 (φ τ) + La (φ τ)) := by
  refine ⟨?_, ?_⟩
  · intro Sg _ _ φ p k hp hk La τ
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hpk1 : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
    have hpk0 : (0 : ℝ) < (p : ℝ) ^ k := by linarith
    set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr
    have hr0 : 0 ≤ r := (inv_pos.mpr hpk0).le
    have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hpk1
    have hgeo : Summable (fun n : ℕ => r ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
    have hterm : ∀ σ n, returnTerm φ p k τ σ n = if (φ ^ (n + 1)) τ = σ then r ^ (n + 1) else 0 := by
      intro σ n
      simp only [returnTerm, one_div, hr]
    have hsum : ∀ σ, Summable (returnTerm φ p k τ σ) := by
      intro σ
      refine Summable.of_norm_bounded hgeo ?_
      intro n
      rw [hterm]
      split_ifs
      · rw [Real.norm_of_nonneg (pow_nonneg hr0 _)]
      · simpa using pow_nonneg hr0 (n + 1)
    have hsum' : ∀ σ, Summable (fun n => returnTerm φ p k τ σ n * La σ) :=
      fun σ => (hsum σ).mul_right _
    have hinner : ∀ n : ℕ, ∑ σ, returnTerm φ p k τ σ n * La σ = r ^ (n + 1) * La ((φ ^ (n + 1)) τ) := by
      intro n
      rw [Finset.sum_eq_single ((φ ^ (n + 1)) τ)]
      · rw [hterm, if_pos rfl]
      · intro b _ hb
        rw [hterm, if_neg (Ne.symm hb), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hswap : ∑ σ, (∑' n, returnTerm φ p k τ σ n) * La σ =
        ∑' n : ℕ, r ^ (n + 1) * La ((φ ^ (n + 1)) τ) := by
      simp_rw [← tsum_mul_right]
      rw [← Summable.tsum_finsetSum (fun σ _ => hsum' σ)]
      exact tsum_congr hinner
    have hlast : ∑ σ, (if σ = τ then 1 / ((p : ℝ) - 1) else 0) * La σ = La τ / ((p : ℝ) - 1) := by
      rw [Finset.sum_eq_single τ]
      · rw [if_pos rfl]; ring
      · intro b _ hb
        rw [if_neg hb, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    simp only [co, sub_mul]
    rw [Finset.sum_sub_distrib, hswap, hlast]
  · intro Sg φ p k hp La q h1 h2 τ
    have hp0 : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : p ≠ 0))
    have a := h1 0 τ
    have b := h2 0 τ
    simp only [zero_add, one_mul, pow_one] at a b
    rw [a, b]
    field_simp
    ring

end GlobalTheory.CompanionTheory.Ar.Num
