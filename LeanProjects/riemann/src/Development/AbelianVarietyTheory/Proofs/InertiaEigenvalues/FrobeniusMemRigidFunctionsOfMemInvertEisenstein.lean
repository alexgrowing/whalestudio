import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem exists_mul_frob_E_eq_one_of_lt (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ)
    (hk : 1 / ((e : ℝ) * l) < k) :
    ∃ g ∈ R O K l k, g * frob K l (E K l e) = 1 := by
  have hl := (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have : NeZero (e * l) := ⟨(Nat.mul_pos (NeZero.pos e) hl).ne'⟩
  have hl0 := l_ne_zero (K := K) l
  have hel : (0 : ℝ) < (e : ℝ) * l := by
    have := NeZero.pos e
    positivity
  have hk0 : 0 < k := lt_trans (by positivity) hk
  let c : K⟦X⟧ := expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) (PowerSeries.mk 1))
  set r : ℝ := (l : ℝ) * rad l k ^ (e * l) with hr
  have hr0 : 0 ≤ r := mul_nonneg (by positivity) (pow_nonneg (rad_nonneg l k) _)
  have hr1 : r < 1 := by
    have h1 : rad l k ^ (e * l) = (l : ℝ) ^ (-(k * ((e : ℝ) * l))) := by
      rw [rad, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg l)]
      push_cast
      ring_nf
    have h2 : (l : ℝ) ^ (-(k * ((e : ℝ) * l))) < (l : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt hl1
      have : 1 < k * ((e : ℝ) * l) := by
        rw [div_lt_iff₀ hel] at hk
        linarith
      linarith
    rw [Real.rpow_neg_one] at h2
    rw [hr, h1]
    calc (l : ℝ) * (l : ℝ) ^ (-(k * ((e : ℝ) * l))) < (l : ℝ) * (l : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left h2 (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hc (n : ℕ) : ‖coeff n c‖ * rad l k ^ n ≤ r ^ (n / (e * l)) := by
    simp only [c]
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨j, rfl⟩ := h
      rw [Nat.mul_div_cancel_left _ (NeZero.pos (e * l)), coeff_rescale, coeff_mk, Pi.one_apply,
        mul_one, norm_pow, norm_neg, norm_inv, norm_l, inv_inv, hr, mul_pow, pow_mul]
    · simpa using pow_nonneg hr0 _
  have hcR : c ∈ R O K l k := mem_R.2 <| squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n)) hc
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (Nat.tendsto_div_const_atTop (NeZero.ne _)))
  refine ⟨C (l : K)⁻¹ * c, mul_mem (HasK.C_mem _) hcR, ?_⟩
  have h := congrArg (fun f => expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) f))
    (mk_one_mul_one_sub_eq_one K)
  simp only [map_mul, map_sub, map_one, rescale_X, expand_X, expand_C, map_neg] at h
  have h2 : (C (l : K)⁻¹ : K⟦X⟧) * l = 1 := by
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  rw [E, map_add, map_pow, frob_X, map_natCast, ← pow_mul, mul_comm l e]
  change c * _ = 1 at h
  linear_combination h + c * h2
end GlobalTheory.BK

namespace GlobalTheory.BK

theorem frob_mem_R_of_mem_invE_A : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := by
  intro O K _ _ _ _ _ l e _ _ _ k hk f hf
  have hk0 : 0 < k := lt_trans (by
    have := NeZero.pos e
    have := (Fact.out : l.Prime).pos
    positivity) hk
  obtain ⟨g, hg, hgE⟩ := exists_mul_frob_E_eq_one_of_lt O K l e k hk
  obtain ⟨n, hn⟩ := mem_away.1 hf
  rw [coe_EIn] at hn
  have h1 : frob K l (E K l e ^ n * f) ∈ R O K l k := A_le_R l hk0 (frob_mem_A l hn)
  have h2 : frob K l f = g ^ n * frob K l (E K l e ^ n * f) := by
    rw [map_mul, map_pow, ← mul_assoc, ← mul_pow, hgE, one_pow, one_mul]
  rw [h2]
  exact mul_mem (pow_mem hg n) h1

end GlobalTheory.BK
