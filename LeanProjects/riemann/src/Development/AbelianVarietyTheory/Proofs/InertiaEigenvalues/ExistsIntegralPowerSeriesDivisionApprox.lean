import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

namespace GlobalTheory.BK.DivApprox

open PowerSeries GlobalTheory.BK

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_mul_le' {f g : K⟦X⟧} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ ≤ a) (hg : ∀ n, ‖coeff n g‖ ≤ b) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ a * b := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    ha hb (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

omit [IsUltrametricDist K] in
theorem eq_low_add_high (f : K⟦X⟧) (n₀ : ℕ) :
    f = (PowerSeries.mk fun n => if n < n₀ then coeff n f else 0) +
      X ^ n₀ * PowerSeries.mk fun n => coeff (n + n₀) f := by
  ext n
  rw [map_add, coeff_mk, coeff_X_pow_mul', coeff_mk]
  by_cases h : n < n₀
  · rw [if_pos h, if_neg (not_le.2 h), add_zero]
  · rw [if_neg h, if_pos (not_lt.1 h), zero_add, Nat.sub_add_cancel (not_lt.1 h)]

theorem exists_inv_mem_A {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {u : K⟦X⟧}
    (hu : u ∈ A O K) (h0 : ‖coeff 0 u‖ = 1) : ∃ w ∈ A O K, u * w = 1 := by
  obtain ⟨v, hv⟩ := (equivA O K).surjective ⟨u, hu⟩
  have hv' : PowerSeries.map (algebraMap O K) v = u := by
    rw [← coe_equivA, hv]
  have hc : algebraMap O K (constantCoeff v) = coeff 0 u := by
    rw [← hv', coeff_map, coeff_zero_eq_constantCoeff_apply]
  have hne : coeff 0 u ≠ 0 := by
    intro h
    rw [h, norm_zero] at h0
    exact zero_ne_one h0
  obtain ⟨c, hc'⟩ := (IsUnitBall.mem_range_iff (O := O) (coeff 0 u)⁻¹).2
    (by rw [norm_inv, h0, inv_one])
  have hunit : IsUnit (constantCoeff v) := by
    refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (O := O) (K := K) ?_)
    rw [map_mul, hc, hc', map_one, mul_inv_cancel₀ hne]
  obtain ⟨w, hw⟩ := (isUnit_iff_constantCoeff.2 hunit).exists_right_inv
  refine ⟨equivA O K w, (equivA O K w).2, ?_⟩
  rw [coe_equivA, ← hv', ← map_mul, hw, map_one]

theorem step {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ t) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ t) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ t) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ t * ρ := by
  have hfe := eq_low_add_high f n₀
  set r : K⟦X⟧ := PowerSeries.mk fun n => if n < n₀ then coeff n f else 0 with hr
  set fh : K⟦X⟧ := PowerSeries.mk fun n => coeff (n + n₀) f with hfh
  have hq : ∀ n, ‖coeff n (w * fh)‖ ≤ t := fun n => by
    have := norm_coeff_mul_le' zero_le_one ht hw (g := fh)
      (fun m => by rw [hfh, coeff_mk]; exact hf _) n
    rwa [one_mul] at this
  refine ⟨w * fh, r, hq, fun i hi => ?_, fun i => ?_, fun n => ?_⟩
  · rw [hr, coeff_mk, if_neg (not_lt.2 hi)]
  · rw [hr, coeff_mk]
    split_ifs
    · exact hf _
    · rwa [norm_zero]
  · have : f - w * fh * g - r = -(w * fh * p) := by
      rw [hg]
      linear_combination hfe - X ^ n₀ * fh * huw
    rw [this, map_neg, norm_neg]
    exact norm_coeff_mul_le' ht hρ hq hp n

theorem iterate {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k : ℕ) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ ρ ^ k := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp, by simp, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨q, r, hq, hr0, hr, he⟩ := ih
    obtain ⟨q', r', hq', hr0', hr', he'⟩ := step hρ (pow_nonneg hρ k) hg huw hw hp _ he
    have h1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ hρ1
    refine ⟨q + q', r + r', fun n => ?_, fun i hi => ?_, fun n => ?_, fun n => ?_⟩
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hq n) ((hq' n).trans h1))
    · rw [map_add, hr0 i hi, hr0' i hi, add_zero]
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr n) ((hr' n).trans h1))
    · have : f - (q + q') * g - (r + r') = f - q * g - r - q' * g - r' := by ring
      rw [this, pow_succ]
      exact he' n

theorem exists_div_approx (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧) (hg : g ∈ A O K) (n₀ : ℕ)
    (h1 : ‖coeff n₀ g‖ = 1) (hlt : ∀ i < n₀, ‖coeff i g‖ < 1) (δ : ℝ) (hδ : 0 < δ)
    (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧
      ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  set ρ : NNReal := (Finset.range n₀).sup (fun i => ‖coeff i g‖₊) with hρ
  have hρ1 : ρ < 1 := by
    rw [hρ, Finset.sup_lt_iff (by simp)]
    intro i hi
    exact_mod_cast hlt i (Finset.mem_range.1 hi)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  obtain ⟨w, hw, huw⟩ := exists_inv_mem_A (O := O)
    (u := PowerSeries.mk fun n => coeff (n + n₀) g)
    (fun n => by rw [coeff_mk]; exact hg _) (by rw [coeff_mk, zero_add, h1])
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hρ1'
  obtain ⟨q, r, hq, hr0, hr, he⟩ := iterate ρ.2 hρ1'.le (eq_low_add_high g n₀) huw hw
    (fun n => by
      rw [coeff_mk]
      split_ifs with h
      · exact_mod_cast Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 h)
      · rw [norm_zero]; exact ρ.2) f hf k
  exact ⟨q, hq, r, hr0, hr, fun n => (he n).trans hk.le⟩

end GlobalTheory.BK.DivApprox
