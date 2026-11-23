import Mathlib

namespace GlobalTheory.PowerSeriesCoeffSum

open MvPowerSeries Finsupp

variable {O : Type} [CommRing O] {a : ℕ}

noncomputable def part (f : MvPowerSeries (Fin a) O) (i : Fin a) : MvPowerSeries (Fin a) O :=
  fun e => if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0

lemma coeff_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (e : Fin a →₀ ℕ) :
    coeff e (part f i) = if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0 := rfl

lemma coeff_X_mul_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if (1 ≤ m i ∧ ∀ j < i, m j = 0) then coeff m f else 0 := by
  rw [X, coeff_monomial_mul, one_mul]
  by_cases h1 : 1 ≤ m i
  · have hle : single i 1 ≤ m := by
      intro k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simp [single_apply, Ne.symm hk]
    rw [if_pos hle, coeff_part, tsub_add_cancel_of_le hle]
    have : (∀ j < i, (m - single i 1 : Fin a →₀ ℕ) j = 0) ↔ (∀ j < i, m j = 0) := by
      refine forall_congr' fun j => imp_congr_right fun hj => ?_
      have : j ≠ i := ne_of_lt hj
      simp [single_apply, Ne.symm this]
    simp only [this, h1, true_and]
  · have hle : ¬ single i 1 ≤ m := by
      intro h; exact h1 (by simpa using h i)
    simp [hle, h1]

lemma eq_sum (f : MvPowerSeries (Fin a) O) (h0 : coeff 0 f = 0) :
    f = ∑ i, X i * part f i := by
  ext m
  rw [map_sum]
  simp only [coeff_X_mul_part]
  by_cases hm : m = 0
  · subst hm; simp [h0]
  · have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm
    set i0 := m.support.min' hne with hi0
    have hi0mem : i0 ∈ m.support := Finset.min'_mem _ _
    have key : ∀ i, (1 ≤ m i ∧ ∀ j < i, m j = 0) ↔ i = i0 := by
      intro i
      constructor
      · rintro ⟨h1, h2⟩
        apply le_antisymm
        · by_contra hlt
          push_neg at hlt
          exact (Finsupp.mem_support_iff.mp hi0mem) (h2 _ hlt)
        · exact Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr (by omega))
      · rintro rfl
        refine ⟨Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi0mem), fun j hj => ?_⟩
        by_contra hj0
        exact absurd (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hj0)) (not_le.mpr hj)
    simp only [key]
    simp

theorem main : ∀ (O : Type) [inst : CommRing O] (a n : ℕ) (f : MvPowerSeries (Fin a) O),
    (∀ (m : Fin a →₀ ℕ), (Finsupp.degree : (Fin a →₀ ℕ) → ℕ) m < n →
      (MvPowerSeries.coeff m : MvPowerSeries (Fin a) O → O) f = (0 : O)) →
    f ∈ Ideal.span (Set.range MvPowerSeries.X) ^ n := by
  intro O _ a n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have h0 : coeff 0 f = 0 := hf 0 (by simp)
    rw [eq_sum f h0, pow_succ']
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih _ ?_)
    intro e he
    rw [coeff_part]
    split_ifs
    · apply hf
      rw [map_add, degree_single]; omega
    · rfl

end GlobalTheory.PowerSeriesCoeffSum
