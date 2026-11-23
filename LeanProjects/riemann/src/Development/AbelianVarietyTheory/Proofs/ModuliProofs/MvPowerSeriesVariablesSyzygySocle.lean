import Mathlib
open scoped TensorProduct

namespace GlobalTheory

open MvPowerSeries Finsupp in
theorem coeff_mul_X_ite {k : Type} [CommRing k] {g : ℕ} (f : MvPowerSeries (Fin g) k)
    (j : Fin g) (m : Fin g →₀ ℕ) :
    coeff m (f * X j) = if m j ≠ 0 then coeff (m - single j 1) f else 0 := by
  classical
  rw [X_def, coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

open MvPowerSeries Finsupp in
theorem mvPowerSeries_X_syzygy {k : Type} [CommRing k] {g : ℕ}
    (r : Fin g → MvPowerSeries (Fin g) k) (hr : ∑ i, r i * X i = 0) :
    ∃ s : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k), s.transpose = -s ∧ (∀ i, s i i = 0) ∧
      r = s.mulVec (fun i => X i) := by
  classical
  let t : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := fun i j n =>
    if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0
  have ht : ∀ i j n, coeff n (t i j) =
      if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0 := fun _ _ _ => rfl
  refine ⟨t - t.transpose, by simp [Matrix.transpose_sub], fun i => by simp, ?_⟩
  funext i
  ext m
  have h1 : ∀ j, coeff m (t i j * X j) =
      if m j ≠ 0 ∧ j < i ∧ ∀ l < j, m l = 0 then coeff m (r i) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht]
    by_cases hj : m j = 0
    · simp [hj]
    · have e : m - single j 1 + single j 1 = m :=
        tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
      have e2 : (∀ l < j, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < j, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, hl.ne']
      simp only [e, e2, hj, ne_eq, not_false_eq_true, if_true, true_and]
  have h2 : ∀ j, coeff m (t j i * X j) =
      if (∀ l < i, m l = 0) ∧ j ≠ i then coeff (m + single i 1) (r j * X j) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht, coeff_mul_X_ite]
    by_cases hji : j = i
    · simp [hji]
    have e0 : (m + single i 1 : Fin g →₀ ℕ) j = m j := by
      simp [Finsupp.single_apply, Ne.symm hji]
    rw [e0]
    by_cases hj : m j = 0
    · simp [hj]
    have e : m - single j 1 + single i 1 = m + single i 1 - single j 1 :=
      tsub_add_eq_add_tsub (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
    rw [e]
    rcases lt_or_gt_of_ne hji with h | h
    · have : ¬ ∀ l < i, m l = 0 := fun H => hj (H j h)
      simp [this, h.not_gt]
    · have e2 : (∀ l < i, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < i, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, (hl.trans h).ne']
      simp only [e2, hj, h, hji, ne_eq, not_false_eq_true, if_true, true_and, and_true]
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.transpose_apply, sub_mul,
    map_sum, map_sub, h1, h2, Finset.sum_sub_distrib]
  by_cases hi : ∀ l < i, m l = 0
  · rw [Finset.sum_eq_zero (fun j _ => if_neg (fun H => H.1 (hi j H.2.1)))]
    have h3 := congrArg (coeff (m + single i 1)) hr
    rw [map_sum, map_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), coeff_mul_X_ite] at h3
    simp only [iff_true_intro hi, true_and]
    rw [← Finset.sum_filter, Finset.filter_ne']
    simp only [Finsupp.add_apply, single_eq_same, add_tsub_cancel_right] at h3
    rw [if_pos (by omega)] at h3
    linear_combination h3
  · simp only [hi, false_and, if_false, Finset.sum_const_zero, sub_zero]
    push_neg at hi
    obtain ⟨l, hl, hml⟩ := hi
    obtain ⟨j, hj, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Fin g)) {j | m j ≠ 0} ⟨l, hml⟩
    have hj0 : ∀ a < j, m a = 0 := fun a ha => by
      by_contra h; exact hmin a h ha
    rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨hj, lt_of_le_of_lt (not_lt.1 (hmin l hml)) hl, hj0⟩]
    · intro b _ hb
      refine if_neg fun H => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · exact H.1 (hj0 b h)
      · exact hj (H.2.2 j h)
    · simp

open MvPowerSeries Finsupp in
theorem mvPowerSeries_prod_X_pow_notMem {k : Type} [CommRing k] [Nontrivial k] {g : ℕ} (N : ℕ) :
    ∏ i, (X i : MvPowerSeries (Fin g) k) ^ N ∉
      Ideal.span (Set.range fun i => (X i : MvPowerSeries (Fin g) k) ^ (N + 1)) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  have hp : ∀ s : Finset (Fin g), ∏ i ∈ s, (X i : MvPowerSeries (Fin g) k) ^ N =
      monomial (∑ i ∈ s, single i N) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have := congrArg (coeff (∑ i : Fin g, single i N)) hc
  rw [hp, coeff_monomial_same, map_sum, Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro i _
    refine X_pow_dvd_iff.1 (dvd_mul_left _ _) _ ?_
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem mvPowerSeries_variables_syzygy_socle :
    ∀ (k : Type) [Field k] (g : ℕ) (x : Fin g → MvPowerSeries (Fin g) k), (∀ i, x i = MvPowerSeries.X i) → (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) ∧ ∀ N : ℕ, ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)) := by
  intro k _ g x hx
  obtain rfl : x = fun i => MvPowerSeries.X i := funext hx
  exact ⟨fun r hr => mvPowerSeries_X_syzygy r hr, fun N => mvPowerSeries_prod_X_pow_notMem N⟩

end GlobalTheory
