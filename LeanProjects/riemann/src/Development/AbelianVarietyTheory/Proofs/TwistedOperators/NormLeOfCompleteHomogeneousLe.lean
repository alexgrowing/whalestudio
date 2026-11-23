import Mathlib

open PowerSeries Finset

namespace GlobalTheory.CompleteHomogeneousBound

def WeightedSummable (r : ℝ) (f : ℂ⟦X⟧) : Prop :=
  Summable fun m : ℕ => ‖coeff m f * (r : ℂ) ^ m‖

theorem WeightedSummable.mul {r : ℝ} {f g : ℂ⟦X⟧} (hf : WeightedSummable r f)
    (hg : WeightedSummable r g) : WeightedSummable r (f * g) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  refine h.congr fun m => ?_
  rw [coeff_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpm : p.1 + p.2 = m := by simpa using hp
  rw [← hpm, pow_add]
  ring

theorem weightedSummable_one (r : ℝ) : WeightedSummable r 1 := by
  refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
  have : m ≠ 0 := by simpa using hm
  simp [coeff_one, this]

theorem weightedSummable_linear (r : ℝ) (b : ℂ) : WeightedSummable r (1 - C b * X) := by
  refine summable_of_ne_finset_zero (s := {0, 1}) fun m hm => ?_
  have h0 : m ≠ 0 := fun h => hm (by simp [h])
  have h1 : m ≠ 1 := fun h => hm (by simp [h])
  simp [coeff_one, coeff_X, h0, h1]

theorem weightedSummable_prod {ι : Type*} (r : ℝ) (s : Finset ι) (f : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, WeightedSummable r (f i)) : WeightedSummable r (∏ i ∈ s, f i) :=
  Finset.prod_induction f (WeightedSummable r) (fun _ _ ha hb => ha.mul hb)
    (weightedSummable_one r) h

theorem weightedSummable_geom_iff (r : ℝ) (b : ℂ) :
    WeightedSummable r (mk fun m => b ^ m) ↔ ‖b * r‖ < 1 := by
  unfold WeightedSummable
  simp only [coeff_mk, ← mul_pow, norm_pow]
  rw [summable_geometric_iff_norm_lt_one, norm_norm]

theorem geom_mul_linear (b : ℂ) : (mk fun m => b ^ m : ℂ⟦X⟧) * (1 - C b * X) = 1 := by
  ext m
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases m with
  | zero => simp
  | succ m => simp [coeff_succ_mul_X, coeff_one, pow_succ]

theorem coeff_prod_geom {n : ℕ} (β : Fin n → ℂ) (m : ℕ) :
    coeff m (∏ i, (mk fun k => β i ^ k : ℂ⟦X⟧)) =
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i := by
  rw [coeff_prod]
  simp only [coeff_mk]
  refine Finset.sum_bij' (fun l _ => (l : Fin n → ℕ))
    (fun a _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using hl
  · intro a ha
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using ha
  · intro l _
    simp
  · intro a _
    simp
  · intro l _
    rfl

theorem norm_le_of_completeHomogeneous_le (n : ℕ) (β : Fin n → ℂ) (c : Fin n → ℝ) (Q : ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcQ : ∀ i, c i ≤ Q)
    (h : ∀ m : ℕ, ‖∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i‖ ≤
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, c i ^ a i) (i : Fin n) : ‖β i‖ ≤ Q := by
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖β i‖ := lt_of_le_of_lt ((hc0 i).trans (hcQ i)) hlt
  set r : ℝ := ‖β i‖⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hpos
  have hc : WeightedSummable r (∏ j, (mk fun k => ((c j : ℝ) : ℂ) ^ k : ℂ⟦X⟧)) := by
    refine weightedSummable_prod r _ _ fun j _ => ?_
    rw [weightedSummable_geom_iff, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (hc0 j), Real.norm_of_nonneg hr0.le, hr, ← div_eq_mul_inv,
      div_lt_one hpos]
    exact (hcQ j).trans_lt hlt
  have hβ : WeightedSummable r (∏ j, (mk fun k => β j ^ k : ℂ⟦X⟧)) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hc
    rw [norm_mul, norm_mul, coeff_prod_geom, coeff_prod_geom]
    refine mul_le_mul_of_nonneg_right ((h m).trans ?_) (norm_nonneg _)
    have : (∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, ((c j : ℝ) : ℂ) ^ a j) =
        ((∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, c j ^ a j : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.norm_real]
    exact le_abs_self _
  have hlin : WeightedSummable r (∏ j ∈ Finset.univ.erase i, (1 - C (β j) * X)) :=
    weightedSummable_prod r _ _ fun j _ => weightedSummable_linear r _
  have hm := hβ.mul hlin
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one (fun j _ => geom_mul_linear (β j)), mul_one, weightedSummable_geom_iff,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, hr, mul_inv_cancel₀ hpos.ne'] at hm
  exact lt_irrefl _ hm

end GlobalTheory.CompleteHomogeneousBound
